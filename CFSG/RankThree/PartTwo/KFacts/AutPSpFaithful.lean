module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open Matrix Module Submodule

variable {r : ℕ} {K : Type} [Field K]

theorem exists_smul_mulVec_eq_of_fieldAut_eq [Finite K] (hr : 1 ≤ r) {σ : K ≃+* K}
    {A : gsp r K} (hA : fieldAut r K σ = conjAut r K A) {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    ∃ a : K, a • (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) =
      fun i => σ (v i) := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p hr
  set L := SpPoint.ofVec v hv with hLdef
  have hLiso := isTotallyIsotropic_line L
  have hσv : (fun i => σ (v i)) ∈ spCoordImage σ L.line :=
    coord_mem_spCoordImage (mem_span_singleton_self v)
  have hσv0 : (fun i => σ (v i)) ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa using this
  have hAv : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈
      L.line.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :=
    Submodule.mem_map_of_mem (mem_span_singleton_self v)
  have hAv0 : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    have h1 := congrArg (fun w => ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) h0
    simp only [mulVec_mulVec, mulVec_zero, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec] at h1
    exact h1
  have hstab : projStabilizer r K (spCoordImage σ L.line) =
      projStabilizer r K (L.line.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) := by
    rw [← map_projStabilizer_fieldAut, ← map_projStabilizer_conjAut, hA]
  have hW := hinj _ _ (fun h0 => hσv0 ((Submodule.eq_bot_iff _).mp h0 _ hσv))
    (isTotallyIsotropic_spCoordImage σ hLiso)
    (fun h0 => hAv0 ((Submodule.eq_bot_iff _).mp h0 _ hAv))
    (isTotallyIsotropic_map_gsp A hLiso) hstab
  rw [hW, hLdef, line_ofVec, Submodule.map_span, Set.image_singleton, mulVecLin_apply,
    Submodule.mem_span_singleton] at hσv
  exact hσv

theorem fieldAut_mem_range_conjAut_iff [Finite K] (hr : 1 ≤ r) {σ : K ≃+* K} :
    fieldAut r K σ ∈ (conjAut r K).range ↔ σ = 1 := by
  classical
  constructor
  · rintro ⟨A, hA⟩
    have hA' := hA.symm
    set i₀ : Fin r ⊕ Fin r := Sum.inl ⟨0, by omega⟩
    set j₀ : Fin r ⊕ Fin r := Sum.inr ⟨0, by omega⟩
    have hij : i₀ ≠ j₀ := Sum.inl_ne_inr
    set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
    set e : Fin r ⊕ Fin r → K := Pi.single i₀ 1
    set e' : Fin r ⊕ Fin r → K := Pi.single j₀ 1
    have he0 : e ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
    have he'0 : e' ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
    have hei : e i₀ = 1 := Pi.single_eq_same _ _
    have hej : e j₀ = 0 := Pi.single_eq_of_ne hij.symm _
    have he'i : e' i₀ = 0 := Pi.single_eq_of_ne hij _
    have he'j : e' j₀ = 1 := Pi.single_eq_same _ _
    have hσe : (fun i => σ (e i)) = e := by
      funext i
      by_cases hi : i = i₀ <;> simp [e, hi]
    have hσe' : (fun i => σ (e' i)) = e' := by
      funext i
      by_cases hi : i = j₀ <;> simp [e', hi]
    obtain ⟨a₁, ha₁⟩ := exists_smul_mulVec_eq_of_fieldAut_eq hr hA' he0
    obtain ⟨a₂, ha₂⟩ := exists_smul_mulVec_eq_of_fieldAut_eq hr hA' he'0
    rw [hσe, ← hM] at ha₁
    rw [hσe', ← hM] at ha₂
    have h1i := congrFun ha₁ i₀
    have h1j := congrFun ha₁ j₀
    have h2i := congrFun ha₂ i₀
    have h2j := congrFun ha₂ j₀
    simp only [Pi.smul_apply, smul_eq_mul, hei, hej, he'i, he'j] at h1i h1j h2i h2j
    have ha₁0 : a₁ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h1i
      exact zero_ne_one h1i
    have ha₂0 : a₂ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h2j
      exact zero_ne_one h2j
    have hu : (M *ᵥ e) j₀ = 0 := (mul_eq_zero.mp h1j).resolve_left ha₁0
    have hw : (M *ᵥ e') i₀ = 0 := (mul_eq_zero.mp h2i).resolve_left ha₂0
    have key : ∀ c : K, σ c = a₁ * c * (M *ᵥ e') j₀ := by
      intro c
      have hv0 : e + c • e' ≠ 0 := by
        intro h0
        have := congrFun h0 i₀
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hei, he'i, mul_zero, add_zero,
          Pi.zero_apply] at this
        exact one_ne_zero this
      obtain ⟨a, ha⟩ := exists_smul_mulVec_eq_of_fieldAut_eq hr hA' hv0
      have hσv : (fun i => σ ((e + c • e') i)) = e + σ c • e' := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
        rw [show σ (e i) = e i from congrFun hσe i, show σ (e' i) = e' i from congrFun hσe' i]
      rw [hσv, ← hM, mulVec_add, mulVec_smul] at ha
      have hai := congrFun ha i₀
      have haj := congrFun ha j₀
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hei, hej, he'i, he'j, hw, hu,
        mul_zero, add_zero, zero_add, mul_one] at hai haj
      have haa : a = a₁ := by
        have hM : (M *ᵥ e) i₀ ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at h1i
          exact zero_ne_one h1i
        have h3 : a * (M *ᵥ e) i₀ = a₁ * (M *ᵥ e) i₀ := by
          rw [h1i]
          exact hai
        exact mul_right_cancel₀ hM h3
      rw [← haj, haa]
      ring
    have h1 := key 1
    rw [map_one, mul_one] at h1
    refine RingEquiv.ext fun c => ?_
    rw [key c, mul_comm a₁ c, mul_assoc, ← h1, mul_one]
    rfl
  · rintro rfl
    rw [map_one]
    exact one_mem _

end CFSG.RankThree.PartTwo.KFacts
