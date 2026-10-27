module

public import CFSG.RankThree.GF2n.Parrott.WAction
public import CFSG.RankThree.GF2n.Parrott.Section2CJ

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem card_CJcomm_eq_eight_of_O3H (h : Tim79a.ParrottHyp z) (x : ↥(O3H D))
    (hx : x ∉ Subgroup.zpowers (⟨sigma1Nine D, sigma1Nine_mem_O3H D⟩ : ↥(O3H D))) :
    Nat.card ↥(CJcomm (z := z) (D := D) (x : ↥(H z))) = 8 :=
  card_CJcomm_eq_eight (z := z) (D := D) h x
    (finrank_fixW_eq_two (z := z) (D := D) h x hx)

end CFSG.RankThree.GF2n.Parrott
