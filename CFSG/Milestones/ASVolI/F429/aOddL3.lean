module

public import CFSG.Milestones.ASVolI.F429.aOddGen
public import CFSG.Milestones.ASVolI.F429.aC3
public import CFSG.Milestones.ASVolI.F4L3Aut

public section

namespace CFSG.ASVolI

section Model

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

theorem burnsideF429a_L3_inner_of_odd {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : Odd f) {β : MulAut (projectiveSL 3 K)}
    (h₀ : ∀ x, β x ∈ (Q3 K 0).map (proj 3 K) ↔ x ∈ (Q3 K 0).map (proj 3 K))
    (h₁ : ∀ x, β x ∈ (Q3 K 1).map (proj 3 K) ↔ x ∈ (Q3 K 1).map (proj 3 K))
    {k : ℕ} (hk : β ^ 2 ^ k = 1) :
    β ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hBD := CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := K)
  have hOG := CFSG.QuasithinUnique.Borel252.L3.overgroupData_L3 (F := K)
  have hN : ∀ x, β x ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 K)) : Set _) ↔
      x ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 K)) : Set _) := by
    rcases hOG.eq_of_between hBD.lt₁ hBD.lt_top₁ with e | e
    · rw [e]
      exact h₀
    · rw [e]
      exact h₁
  have hV : ∀ x, x ∈ (V1 : Subgroup (projectiveSL 3 K)) ↔ β x ∈ (V1 : Subgroup (projectiveSL 3 K)) :=
    (CFSG.Quasithin.H13.F431.mem_autStab_iff_of_normalizer hBD.core₁ β).mp
      (fun y => (hN y).symm)
  have hS : β ∈ semilinearAutGroup 3 K :=
    CFSG.Quasithin.H13.F431.L3.P3.mem_semilinear_of_map_V1 (fun g hg => (hV g).mp hg)
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp hS
  have hσk : σ ^ 2 ^ k = 1 := by
    have hE : ∀ e : ↥(semilinearAutGroup 3 K),
        (semilinearAutGroup 3 K).subtype e ∈ semilinearAutGroup 3 K := fun e => e.2
    have hfp : burnsideF447_fpE hE (⟨β, hS⟩ : ↥(semilinearAutGroup 3 K)) = σ :=
      burnsideF447_fpE_eq hE hAσ
    have hθ : (⟨β, hS⟩ : ↥(semilinearAutGroup 3 K)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hk
    rw [← hfp, ← map_pow, hθ, map_one]
  have hσf : σ ^ f = 1 := CFSG.Quasithin.H13.F431.L3.P3.autField_pow_eq_one hf.pos hK σ
  have hσ : σ = 1 := by
    have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσk
    have h2 : orderOf σ ∣ f := orderOf_dvd_of_pow_eq_one hσf
    have h3 : Nat.Coprime (2 ^ k) f := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hf)
    have h4 : orderOf σ ∣ Nat.gcd (2 ^ k) f := Nat.dvd_gcd h1 h2
    rw [h3.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hlin : β ∈ linearAutGroup 3 K := by
    rw [hAσ, hσ, map_one, mul_one]
    exact conjAut_mem_linearAutGroup A
  refine CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (fun h => ?_) β
    hlin k ?_
  · have := h.trans (Nat.gcd_dvd_left 3 _)
    omega
  · rw [hk]
    exact Subgroup.one_mem _

end Model

section Main

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ASVolI.ChF.ClassicalRoots
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

theorem burnsideF429a_two_le_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : Odd f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 → r ∈ Gp := by
  intro r hr k hk
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .L3) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = 2 ^ f := by simpa using marking.field_card
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have e0 := burnsideF429a_L3_parabolic marking false
  have e1 := burnsideF429a_L3_parabolic marking true
  simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
  refine burnsideF429a_mem_of_model₂ hyp.centralizer_trivial (burnsideF429a_L3_Psi marking)
    (h1.trans e0) (h2.trans e1) hr (fun β hβ₁ hβ₂ hβr => ?_)
  exact burnsideF429a_L3_inner_of_odd hK hf hβ₁ hβ₂
    (burnsideF429a_pow_eq_one_of_intertwine _ hβr hk)

end Main

end CFSG.ASVolI
