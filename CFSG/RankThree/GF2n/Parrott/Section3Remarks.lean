module

public import CFSG.RankThree.GF2n.Parrott.Section3RemarksT
public import CFSG.RankThree.GF2n.Parrott.Section3RemarksJ

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G] [Finite G] {z : G}

section Remarks

variable (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
  (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
  (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
  (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
  (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range)
  {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = ⟨sigma1, sigma1_mem_A⟩) (hσ₂ : φ σ₂ = ⟨sigma2, sigma2_mem_A⟩)
  (h3₁ : orderOf σ₁ = 3) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
  (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
  (hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ₁) (hu : ∃ u' : ↥(H z), u' * σ₁ * u'⁻¹ = σ₂)

include hJ hcard hcomm hCHJ hker hQP hσ₁ hσ₂ h3₁ h3₂ hc hne hy hu

omit hker hQP hσ₁ hσ₂ in
theorem nonempty_CJ_sigma1_mulEquiv_quaternion :
    Nonempty (CJ z (σ₁ : G) ≃* QuaternionGroup 2) := by
  obtain ⟨y, hy9, hyσ⟩ := hy
  obtain ⟨u, hu⟩ := hu
  have h8₁ := card_CJ_eq_eight_of_cube hJ hcard hcomm hCHJ hy9 hyσ
  have h8₂ : Nat.card (CJ z (σ₂ : G)) = 8 := by
    rw [← hu]
    change Nat.card (CJ z ((u : G) * σ₁ * (u : G)⁻¹)) = 8
    rw [card_CJ_conj_eq, h8₁]
  exact (nonempty_CJ_mulEquiv_quaternion hJ hcomm h3₁ h3₂ hc h8₁ h8₂ hne).1

omit h3₁ in
theorem CJ_sigma1_mul_sigma2_eq : CJ z ((σ₁ * σ₂ : ↥(H z)) : G) = Subgroup.zpowers z := by
  obtain ⟨y, hy9, hyσ⟩ := hy
  obtain ⟨u, hu⟩ := hu
  exact CJ_sigma1_mul_sigma2_eq_zpowers hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy9 hyσ
    hu

omit hker hQP hσ₁ hσ₂ h3₁ in
theorem commutator_J_H_eq_J : ⁅J z, H z⁆ = J z := by
  obtain ⟨y, hy9, hyσ⟩ := hy
  obtain ⟨u, hu⟩ := hu
  exact commutator_J_H_eq_J_of hJ hcard hcomm hCHJ h3₂ hc hne hy9 hyσ hu

end Remarks

end CFSG.RankThree.GF2n.Parrott.Remarks
