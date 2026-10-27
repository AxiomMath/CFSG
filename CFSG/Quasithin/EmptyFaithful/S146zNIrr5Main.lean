module

public import CFSG.Quasithin.EmptyFaithful.S146zNIrr5Def
public import CFSG.Quasithin.EmptyFaithful.S146zNIrr5C
public import CFSG.Quasithin.EmptyFaithful.S146zNIrr5D

public section

namespace CFSG.Quasithin

theorem a6NoIrr5_proved : A6NoIrr5 := by
  intro V _ _ hV hcard L ⟨e⟩ hirr
  have hL : Nat.card L = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  obtain ⟨T, hT, ⟨t, htT, ht1⟩, hn⟩ := A6Irr5.exists_invariant_finset hV hcard L hL
  rcases hn with h1 | h6
  · exact ht1 (A6Irr5.eq_one_of_invariant_finset hV hcard hirr hT (by omega) t htT)
  · exact A6Irr5.false_of_invariant_six hV hcard hirr hT h6

end CFSG.Quasithin
