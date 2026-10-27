module

public import CFSG.Quasithin.Background.E2Two
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem card_of_isPSL_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_isAlt_six {X : Type} [Group X] (h : IsAlt 6 X) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_of_shape_two_b {X : Type} [Group X] (h : IsPSL 3 2 1 X ∨ E2.IsSp4Prime 1 X) :
    Nat.card X = 168 ∨ Nat.card X = 360 := by
  rcases h with h | h
  · exact Or.inl (card_of_isPSL_three_two h)
  · right
    have h' : IsAlt 6 X := by
      simpa [E2.IsSp4Prime] using h
    exact card_of_isAlt_six h'

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSp4Prime_one_iff {X : Type} [Group X] : E2.IsSp4Prime 1 X ↔ IsAlt 6 X := by
  simp [E2.IsSp4Prime]

end CFSG.Quasithin.GoldS146R
