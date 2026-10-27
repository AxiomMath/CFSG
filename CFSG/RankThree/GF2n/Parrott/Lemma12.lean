module

public import CFSG.RankThree.GF2n.Parrott.Section2Cases

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem not_isConj_sigma1Nine_of_mem_zpowers_sigma1_mul_sigma2_inv
    {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    {y : ↥(H z)}
    (hy : y ∈ Subgroup.zpowers (sigma1Nine (z := z) D * σ₂⁻¹)) :
    ¬ IsConj (sigma1Nine (z := z) D) y :=
  not_isConj_of_mem_zpowers_sigma1_mul_sigma2_inv_of_hom (qH D) (qH_sigma1Nine (z := z) D) hq₂ hy

theorem orderOf_mul_sigma2_inv_of_commute {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
  orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order (z := z) D) hσ₂
    (qH_sigma1Nine (z := z) D) hq₂ hcomm

end CFSG.RankThree.GF2n.Parrott

