module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem false_of_card_Lbar_le_four (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h4 : Nat.card (Lbar S a) ≤ 4) : False := by
  have hlt := h.four_lt_card_Lbar
  omega

end CFSG.RankThree.GF2n.Stroth78
