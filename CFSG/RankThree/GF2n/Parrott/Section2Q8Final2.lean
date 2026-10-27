module

public import CFSG.RankThree.GF2n.Parrott.Section2Q8Final
public import CFSG.RankThree.GF2n.Parrott.CommutatorNormalSigma1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem card_CJcomm_sigma1sigma2inv_eq_eight_final (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    Nat.card ↥(CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂⁻¹)) = 8 :=
  card_CJcomm_sigma1sigma2inv_eq_eight_of_lift (z := z) (D := D) h hσ₂ hq₂ hc₂
    (fun g p hp =>
      commutator_sigma1Nine_conj_mem (z := z) (D := D) h hEq hσ₂ hq₂ hc₂ g p hp)

end CFSG.RankThree.GF2n.Parrott
