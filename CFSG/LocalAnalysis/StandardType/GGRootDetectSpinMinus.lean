module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
public import CFSG.LieType.Universal.Spin.Twisted.Datum

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LieType.Steinberg.SpinFrame QuadraticMap
open scoped Matrix

namespace RootDetectSpin

variable {n : ℕ} {K : Type} [Field K]

@[expose] def minusIdx (m : Fin (n - 1)) : Bool → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  | true => .inl m
  | false => .inr (.inl m)

theorem isCoordFrame_minusFrame (b c : K) :
    IsCoordFrame (minusFrame n b c).toHypFrame (minusIdx (n := n)) where
  vec_eq m r := by cases r <;> rfl
  polar_eq v m r := by
    cases r
    · exact polar_quadMinus_single_inr_inl n K b c v m
    · exact polar_quadMinus_single_inl n K b c v m

theorem minus_b_ne_zero [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' c
  apply hirr r
  rw [zero_mul, add_zero, _root_.sq, hr, CharTwo.add_self_eq_zero]

theorem map_mulVec_of_fixed {ι : Type} [Fintype ι] (A : Matrix ι ι K) (φ : K ≃+* K)
    {v : ι → K} (hv : ∀ k, φ (v k) = v k) : A.map φ *ᵥ v = fun k => φ ((A *ᵥ v) k) := by
  funext k
  have hv' : (⇑φ.toRingHom ∘ v) = v := funext hv
  have h := RingHom.map_mulVec φ.toRingHom A v k
  rw [hv'] at h
  exact h.symm

theorem detect_short [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (σ₀ : Bool) (N : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) (φ : K ≃+* K)
    (h : ∀ z ∈ (twShortRoot n hirr i σ₀).range, spinMatrix (quadMinus n K b c) z * N =
      N * glFieldEquiv _ φ (spinMatrix (quadMinus n K b c) z)) : φ = 1 := by
  have hb := minus_b_ne_zero hirr
  have hφb : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  obtain ⟨u, hu⟩ : ∃ u : Vm n K, u = minusVec n i σ₀ := ⟨_, rfl⟩
  have hu' : u = Pi.single (minusIdx i σ₀) 1 := by
    rw [hu]
    exact (isCoordFrame_minusFrame (n := n) b c).vec_eq i σ₀
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Vm n K, z₀ = planeVec n planeOne := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Vm n K, y = planeVec n ![0, 1] := ⟨_, rfl⟩
  set kz : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := .inr (.inr 0) with hkz
  set ku : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := minusIdx i σ₀ with hku
  have hku_ne : ku ≠ kz := by
    rw [hku, hkz]
    cases σ₀ <;> simp [minusIdx]
  have hukz : u kz = 0 := by rw [hu', Pi.single_apply, ite_eq_right_iff.mpr fun h => absurd h.symm hku_ne]
  have huku : u ku = 1 := by rw [hu', Pi.single_eq_same]
  have hz₀kz : z₀ kz = 1 := by rw [hz₀, hkz]; simp [planeVec, planeOne]
  have hz₀ku : z₀ ku = 0 := by rw [hz₀, hku]; cases σ₀ <;> simp [planeVec, minusIdx]
  have hufix : ∀ k, φ (u k) = u k := by
    intro k
    rw [hu', Pi.single_apply]
    split_ifs <;> simp
  have hyfix : ∀ k, φ (y k) = y k := by
    intro k
    rw [hy]
    rcases k with k | k | k
    · simp [planeVec]
    · simp [planeVec]
    · fin_cases k <;> simp [planeVec]
  have hyu : polar (quadMinus n K b c) y u = 0 := by
    rw [hy, hu]
    exact polar_planeVec_minusVec n b c _ i σ₀
  have hyz : polar (quadMinus n K b c) y z₀ = b := by
    rw [hy, hz₀, polar_planeVec_planeVec]
    simp [polarPlane, planeOne]
  have hact : ∀ (t : K) (v : Vm n K),
      spinAction (quadMinus n K b c) (twShortRoot n hirr i σ₀ (.ofAdd (t • planeOne))) v =
        v + (t * polar (quadMinus n K b c) v u) • z₀ -
          (t * polar (quadMinus n K b c) v z₀) • u -
            (t ^ 2 * polar (quadMinus n K b c) v u) • u := by
    intro t v
    have hn : planeNorm b c (t • planeOne : Fin 2 → K) = t ^ 2 := by
      simp [planeNorm, planeOne]
    rw [spinAction_twShortRoot, planeVec_smul, polar_smul_right, hn, ← hu, ← hz₀, smul_smul,
      mul_comm (polar (quadMinus n K b c) v u) t, smul_eq_mul]
  obtain ⟨Nm, hNm⟩ : ∃ Nm : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K, Nm = N.val := ⟨_, rfl⟩
  have key : ∀ t : K, spinAction (quadMinus n K b c)
      (twShortRoot n hirr i σ₀ (.ofAdd (t • planeOne))) (Nm *ᵥ y) =
        Nm *ᵥ y - (φ t * φ b) • (Nm *ᵥ u) := by
    intro t
    have h1 := congrArg (fun A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K => A.val *ᵥ y)
      (h _ ⟨Multiplicative.ofAdd (t • planeOne), rfl⟩)
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, ← hNm] at h1
    rw [spinMatrix_mulVec, RootDetectSpin.coe_glFieldEquiv, map_mulVec_of_fixed _ φ hyfix,
      spinMatrix_mulVec, hact t y, hyu, hyz] at h1
    rw [h1]
    have hv : (fun k => φ ((y + (t * 0) • z₀ - (t * b) • u - (t ^ 2 * 0) • u) k)) =
        y - (φ t * φ b) • u := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero, zero_mul,
        add_zero, sub_zero, map_sub, map_mul, hyfix, hufix]
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_smul]
  obtain ⟨β₁, hβ₁⟩ : ∃ β : K, β = polar (quadMinus n K b c) (Nm *ᵥ y) u := ⟨_, rfl⟩
  obtain ⟨β₂, hβ₂⟩ : ∃ β : K, β = polar (quadMinus n K b c) (Nm *ᵥ y) z₀ := ⟨_, rfl⟩
  have hEz : ∀ t : K, t * β₁ = -(φ t * φ b * (Nm *ᵥ u) kz) := by
    intro t
    have h2 := congrFun (key t) kz
    rw [hact, ← hβ₁, ← hβ₂] at h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz₀kz, hukz, mul_one,
      mul_zero, sub_zero] at h2
    linear_combination h2
  have hEu : ∀ t : K, -(t * β₂) - t ^ 2 * β₁ = -(φ t * φ b * (Nm *ᵥ u) ku) := by
    intro t
    have h2 := congrFun (key t) ku
    rw [hact, ← hβ₁, ← hβ₂] at h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz₀ku, huku, mul_one,
      mul_zero, add_zero] at h2
    linear_combination h2
  have hw0 : Nm *ᵥ u ≠ 0 := by
    intro h0
    have h3 : (N⁻¹ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).val *ᵥ (Nm *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, hNm, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h3
    have h4 := congrFun h3 ku
    rw [huku] at h4
    exact zero_ne_one h4
  have hE1 := hEz 1
  have hU1 := hEu 1
  rw [map_one] at hE1 hU1
  refine RingEquiv.ext fun t => ?_
  show φ t = t
  by_cases h1 : β₁ = 0
  · by_cases h2 : β₂ = 0
    · exfalso
      apply hw0
      have h4 := key 1
      rw [hact, ← hβ₁, ← hβ₂, h1, h2] at h4
      simp only [mul_zero, zero_smul, add_zero, sub_zero, map_one, one_mul] at h4
      exact (smul_eq_zero.mp (sub_eq_self.mp h4.symm)).resolve_left hφb
    · have h3 := hEu t
      have h5 : t * β₂ = φ t * β₂ := by
        rw [h1] at h3 hU1
        linear_combination -h3 + φ t * hU1
      exact (mul_right_cancel₀ h2 h5).symm
  · have h3 := hEz t
    have h5 : t * β₁ = φ t * β₁ := by linear_combination h3 - φ t * hE1
    exact (mul_right_cancel₀ h1 h5).symm

theorem rootDetectAt_spinMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (q : ℕ → Prop) :
    RootDetectAt ⟨spinGroup (quadMinus n F b c), minusDatum n hirr⟩ q := by
  intro G _ _ ψ hker p hp hp2 _ c' hc hcp γ hγ u hT
  have : Finite (spinGroup (quadMinus n F b c)) :=
    Finite.of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinMatrix_quadMinus_eq_bot (n := n) hirr CharTwo.two_eq_zero))
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨hsurj, -, hZ⟩ := spinToStatedProj_quadMinus hn hirr
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite n F hirr
  have hT3 := CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadMinus hn F b c
  refine ggPsiInnerDiag_spin_of_aut (range_spinMatrix_quadMinus hn hirr)
    (isPerfect_spinGroup_quadMinus hn hirr).commutator_eq_top hsurj hZ
    (mul_self_mem_statedOmega (coe_quadMinus n F b c) hnd hT3)
    (eq_one_of_mk_eq_one (coe_quadMinus n F b c) hnd) (hp.odd_of_ne_two hp2)
    (fun β _ => CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_minus
      ⟨Nat.prime_two, hf, hn⟩ hF hirr β) (minusDatum n hirr) ?_ hker hc hcp hT
  intro N φ hN
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hst⟩ | ⟨i, s, hs⟩
  · obtain ⟨hmat, hE0, hEφ⟩ := longRoot_hroot (isCoordFrame_minusFrame (n := n) b c) hij s t
    exact detect_of_linear (X := (minusDatum n hirr).rootGroup γ)
      (x := fun a => (minusFrame n b c).longRoot hij s t (.ofAdd a))
      (fun a => longRoot_mem_minusRootGroup n hirr hij s t hst a) hmat hE0 hEφ N φ hN
  · refine detect_short hirr i s N φ fun z hz => hN z ?_
    change z ∈ minusRootGroup n hirr γ
    rw [minusRootGroup_eq_short n hirr i s hs]
    exact hz

end RootDetectSpin

section Family

theorem ggRootDetect_pOmegaMinus : GGRootDetect .POmegaMinus := by
  refine ggRootDetect_of_rootDetectAt fun n f hadm _ => ?_
  obtain ⟨-, hf, hn⟩ := hadm
  exact RootDetectSpin.rootDetectAt_spinMinus hn hf (GaloisField.card 2 f (by omega))
    (minusCoeffs_irr 2 f) _

end Family

end CFSG.StandardType
