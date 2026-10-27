module

public import CFSG.Quasithin.H13.VolIAltCoverG2

public section

namespace CFSG.Quasithin.LRed8

open CFSG.Quasithin

theorem card_fixV_g2
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hcomm : commV L = ⊤)
    (h : G2NaturalDerived L ⊤ (fixV L ⊓ ⊤) 1) : Nat.card (fixV L) ≤ 2 := by
  rcases H13.VolI.g2NaturalCover_holds V hV L (fixV L ⊓ ⊤) inf_le_left hcomm h with h1 | ⟨h2, -, -⟩
  · rw [inf_top_eq] at h1
    rw [h1, Subgroup.card_bot]
    norm_num
  · rw [inf_top_eq] at h2
    exact h2.le

end CFSG.Quasithin.LRed8
