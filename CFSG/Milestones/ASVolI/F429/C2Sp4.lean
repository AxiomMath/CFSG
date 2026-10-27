module

public import CFSG.Milestones.ASVolI.F429.C2L3
public import CFSG.Milestones.ASVolI.F429.aOddSp4
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSp
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ASVolI.ChF.ClassicalRoots
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Lin2.Five CFSG.ComponentClassification.OuterAutomorphisms

section SpModel

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem burnsideF429_Sp4_field_descent (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {β : MulAut (StatedProj (StatedSp 2 K))}
    (h₀ : ∀ x, β x ∈ (Q2 K 0).map (proj 2 K) ↔ x ∈ (Q2 K 0).map (proj 2 K))
    (hβ2 : β ^ 2 = 1)
    (hout : β ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range) :
    Even f ∧ ∃ (H : gsp 2 K) (σ : K ≃+* K), (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧
      β = conjAut 2 K H * fieldAut 2 K σ * (conjAut 2 K H)⁻¹ := by
  have hproj : Function.Injective (proj 2 K) := fun a b h => (projEquiv K).injective h
  have hPβ : ((Q2 K 0).map (proj 2 K)).map β.toMonoidHom = (Q2 K 0).map (proj 2 K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h₀ y).mpr hy
    · intro hx
      refine ⟨β⁻¹ x, (h₀ _).mp ?_, by simp⟩
      simpa using hx
  have hZ : (ctr (oPPrime 2 ((Q2 K 0).map (proj 2 K)))).map β.toMonoidHom =
      ctr (oPPrime 2 ((Q2 K 0).map (proj 2 K))) := by
    rw [← burnsideF429a_ctr_map (φ := β.toMonoidHom) β.injective,
      ← burnsideF4gU4Inv_oPPrime_map (ψ := β.toMonoidHom) β.injective, hPβ]
  have hZX : ctr (oPPrime 2 ((Q2 K 0).map (proj 2 K))) =
      (burnsideF4gSpInv_Xl K).map (proj 2 K) := by
    rw [burnsideF4gU4Inv_oPPrime_map hproj, burnsideF429a_ctr_map hproj, burnsideF429a_Sp_ctr_L1]
  have hmem : β (proj 2 K (burnsideF4gSpInv_xl 1)) ∈ (burnsideF4gSpInv_Xl K).map (proj 2 K) := by
    rw [← hZX, ← hZ]
    refine ⟨_, ?_, rfl⟩
    rw [hZX]
    exact ⟨_, burnsideF4gSpInv_mem_Xl.2 ⟨1, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xl.1 hy
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow β
  have hε0 : ε = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with h | h
    · exact h
    · exfalso
      rw [h, pow_one] at hβ
      rw [hβ] at hyx
      exact burnsideF429a_Sp_tau_not_mem_Xl A σ t hyx.symm
  rw [hε0, pow_zero, mul_one] at hβ
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    apply hout
    have hcA := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
    rw [hβ, hσ1, map_one, mul_one]
    exact hcA
  have hα : (conjAut 2 K A * fieldAut 2 K σ) ^ 2 = 1 := by rw [← hβ]; exact hβ2
  obtain ⟨hord, H, hH⟩ :=
    CFSG.StandardType.RecipeFieldSpU.conjAut_mul_fieldAut_of_pow_eq_one (by norm_num)
      Nat.prime_two A σ hσ1 hα
  have hσσ : σ * σ = 1 := by
    rw [← pow_two, ← hord]
    exact pow_orderOf_eq_one σ
  obtain ⟨hfe, hσpow⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf hK hσ1 hσσ
  exact ⟨hfe, H, σ, hσpow, hβ.trans hH⟩

end SpModel

section Sp4Coordinates

private noncomputable def burnsideF429_spΨ {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .Sp4 2 f H) : StatedProj (StatedSp 2 marking.field) ≃* H :=
  marking.identification

private noncomputable def burnsideF429_spE (f : ℕ) (K : Type) [Field K] :
    StatedSp 2 K ≃* nativeGroup .Sp4 (2 ^ f) K :=
  MulEquiv.refl _

private noncomputable def burnsideF429_spGL (K : Type) [Field K] :
    GL (Fin 2 ⊕ Fin 2) K ≃* GL (Coord .Sp4) K :=
  MulEquiv.refl _

private theorem burnsideF429_spE_transport {f : ℕ} {H : Type} [Group H]
    (mk : ClassicalRoots.Marking .Sp4 2 f H) (x : StatedSp 2 mk.field) :
    mk.transport (burnsideF429_spE f mk.field x) = burnsideF429_spΨ mk (proj 2 mk.field x) :=
  rfl

private theorem burnsideF429_spE_ident {f : ℕ} {H : Type} [Group H]
    (mk : ClassicalRoots.Marking .Sp4 2 f H) (x : StatedSp 2 mk.field) :
    mk.identification (projectiveMap .Sp4 (2 ^ f) mk.field (burnsideF429_spE f mk.field x)) =
      burnsideF429_spΨ mk (proj 2 mk.field x) :=
  rfl

private theorem burnsideF429_spE_conjSp {f : ℕ} {K : Type} [Field K] (H : gsp 2 K)
    (g : StatedSp 2 K) :
    ((burnsideF429_spE f K (conjSp 2 K H g) : nativeGroup .Sp4 (2 ^ f) K) : GL (Coord .Sp4) K) =
      burnsideF429_spGL K (H : GL (Fin 2 ⊕ Fin 2) K) *
        ((burnsideF429_spE f K g : nativeGroup .Sp4 (2 ^ f) K) : GL (Coord .Sp4) K) *
        (burnsideF429_spGL K (H : GL (Fin 2 ⊕ Fin 2) K))⁻¹ :=
  coe_conjSp H g

private theorem burnsideF429_spE_fieldSp {f : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (g : StatedSp 2 K) :
    ((burnsideF429_spE f K (fieldSp 2 K σ g) : nativeGroup .Sp4 (2 ^ f) K) :
        GL (Coord .Sp4) K).val =
      ((burnsideF429_spE f K g : nativeGroup .Sp4 (2 ^ f) K) : GL (Coord .Sp4) K).val.map
        σ.toRingHom :=
  coe_fieldSp σ g

private theorem burnsideF429_spNative_map_conj {f : ℕ} {K : Type} [Field K] (H : gsp 2 K) :
    (nativeGroup .Sp4 (2 ^ f) K).map
        (MulAut.conj (burnsideF429_spGL K (H : GL (Fin 2 ⊕ Fin 2) K))).toMonoidHom =
      nativeGroup .Sp4 (2 ^ f) K := by
  show (StatedSp 2 K).map (MulAut.conj (H : GL (Fin 2 ⊕ Fin 2) K)).toMonoidHom = StatedSp 2 K
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact conj_mem_statedSp H.2 hB
  · intro hA
    refine ⟨(H : GL (Fin 2 ⊕ Fin 2) K)⁻¹ * A * (H : GL (Fin 2 ⊕ Fin 2) K), ?_,
      by simp [mul_assoc]⟩
    have := conj_mem_statedSp (H⁻¹ : gsp 2 K).2 hA
    simpa [mul_assoc] using this

private theorem burnsideF429_Sp4_parabolic {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .Sp4 2 f H) (b : Bool) :
    marking.parabolic b = ((Q2 marking.field (if b then 1 else 0)).map (proj 2 marking.field)).map
      (burnsideF429_spΨ marking).toMonoidHom := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSpOne_mem_rawStabilizer, burnsideF4gSpOne_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSpOne_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSpOne_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSpOne_coordinateSpace_flag v).2)
  have e1 : marking.parabolic b =
      (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
    congrArg (Subgroup.map marking.transport) key
  refine e1.trans ?_
  exact (Subgroup.map_map _ _ _).symm

end Sp4Coordinates

section Payload

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}


private theorem burnsideF429_c2c_Sp4_aux {f : ℕ} (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) {t : E} (htT : t ∈ T)
    (htS : t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (htt : t * t = 1) :
    hyp.toHypF_4_4g.chart.IsFieldInv t := by
  haveI := hyp.finite
  haveI := hyp.normal
  have htG : t ∉ Gp := fun h => htS (by rw [← burnsideF429_T_inf_Gp hyp hT]; exact ⟨htT, h⟩)
  have htM : t ∈ M₁ ⊓ M₂ := hT.1 htT
  have hf1 : 1 ≤ f := hyp.model.2.1
  have hfits := hyp.toHypF_4_4g.chart.coordinatePayload_fits
  have hm := hyp.toHypF_4_4g.chart_matches
  unfold NativeChart.IsFieldInv
  refine ⟨htG, htt, ?_⟩
  generalize hcp : hyp.toHypF_4_4g.chart.coordinatePayload = cp at hfits ⊢
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .Sp4 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    have hK : Nat.card mk.field = 2 ^ f := by simpa using mk.field_card
    haveI : CharP mk.field 2 := burnsideF4gSp_charP_of_card hK
    set Ψ := burnsideF429_spΨ mk with hΨ
    have e0 := burnsideF429_Sp4_parabolic mk false
    have e1 := burnsideF429_Sp4_parabolic mk true
    simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
    have h₁ : M₁.subgroupOf Gp = ((Q2 mk.field 0).map (proj 2 mk.field)).map Ψ.toMonoidHom := by
      rw [← e0]
      exact burnsideF429_subgroupOf_eq_of_inf (hm.2.1.trans hpts)
    have h₂ : M₂.subgroupOf Gp = ((Q2 mk.field 1).map (proj 2 mk.field)).map Ψ.toMonoidHom := by
      rw [← e1]
      exact burnsideF429_subgroupOf_eq_of_inf (hm.2.2.trans hlns)
    obtain ⟨β, hβ₀, -, hβ⟩ := burnsideF429_model_aut Ψ h₁ h₂ htM
    have hβ2 : β ^ 2 = 1 :=
      burnsideF429a_pow_eq_one_of_intertwine Ψ hβ (n := 2) (by rw [pow_two]; exact htt)
    have hout : β ∉ (MulAut.conj : StatedProj (StatedSp 2 mk.field) →* MulAut _).range :=
      fun hin => htG (burnsideF429_mem_of_inner hyp.centralizer_trivial Ψ hβ hin)
    obtain ⟨hfe, H, σ, hσpow, hβeq⟩ := burnsideF429_Sp4_field_descent hK hf1 hβ₀ hβ2 hout
    obtain ⟨d, hd⟩ := hfe
    refine ⟨d, by omega, by omega, ?_⟩
    set conj : MulAut ↥Gp := (Ψ.symm.trans (conjAut 2 mk.field H)).trans Ψ with hconj
    have hconjΨ : ∀ y, conj (Ψ y) = Ψ (conjAut 2 mk.field H y) := by
      intro y
      show Ψ (conjAut 2 mk.field H (Ψ.symm (Ψ y))) = _
      rw [MulEquiv.symm_apply_apply]
    refine ⟨conj, ⟨burnsideF429_spGL mk.field (H : GL (Fin 2 ⊕ Fin 2) mk.field),
      burnsideF429_spNative_map_conj H, ?_⟩, ⟨Or.inr rfl, σ.toRingHom, ?_, ?_⟩⟩
    · intro r
      obtain ⟨g, rfl⟩ := (burnsideF429_spE f mk.field).surjective r
      refine ⟨burnsideF429_spE f mk.field (conjSp 2 mk.field H g),
        burnsideF429_spE_conjSp H g, ?_⟩
      rw [burnsideF429_spE_transport, burnsideF429_spE_transport, ← conjAut_proj, hconjΨ]
    · intro x
      rw [show d = f / 2 by omega]
      exact hσpow x
    · intro r
      obtain ⟨g, rfl⟩ := (burnsideF429_spE f mk.field).surjective r
      refine ⟨burnsideF429_spE f mk.field (fieldSp 2 mk.field σ g),
        burnsideF429_spE_fieldSp σ g, ?_⟩
      show ((conj (mk.identification (projectiveMap .Sp4 (2 ^ f) mk.field
          (burnsideF429_spE f mk.field (fieldSp 2 mk.field σ g)))) : ↥Gp) : E) =
        t * ((conj (mk.identification (projectiveMap .Sp4 (2 ^ f) mk.field
          (burnsideF429_spE f mk.field g))) : ↥Gp) : E) * t⁻¹
      rw [burnsideF429_spE_ident, burnsideF429_spE_ident, hconjΨ, hconjΨ, ← hβ, hβeq]
      simp only [MulAut.mul_apply, MulAut.inv_apply]
      rw [MulEquiv.symm_apply_apply, fieldAut_proj]
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

theorem burnsideF429_c2c_Sp4 {f : ℕ} (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) {t : E} (htT : t ∈ T)
    (htS : t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (htt : t * t = 1) :
    hyp.toHypF_4_4g.chart.IsFieldInv t :=
  burnsideF429_c2c_Sp4_aux hyp hT htT htS htt

end Payload

end CFSG.ASVolI
