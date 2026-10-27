module

public import CFSG.Permutation.FiveTransitive.Helpers

public section

namespace CFSG

namespace FiveTransitive.LowDegreeClassification

theorem classification_of_five_transitive_of_card_le_thirteen
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X) (hcard_le : Fintype.card X ≤ 13)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    let n := Fintype.card X
    Fintype.card G = n.factorial ∨
    (7 ≤ n ∧ Fintype.card G = n.factorial / 2) ∨
    (n = 12 ∧ Fintype.card G = 95040) ∨
    (n = 24 ∧ Fintype.card G = 244823040) := by
  classical
  dsimp only
  by_cases h11 : Fintype.card X ≤ 11
  · rcases Helpers.classification_of_five_transitive_of_card_le_eleven
        G X hcard h11 h5 with hSym | hAlt
    · exact Or.inl hSym
    · exact Or.inr (Or.inl hAlt)
  by_cases h12 : Fintype.card X = 12
  · rcases Helpers.classification_of_five_transitive_of_card_eq_twelve
        G X h12 h5 with hSym | hAlt | hM12
    · exact Or.inl hSym
    · exact Or.inr (Or.inl hAlt)
    · exact Or.inr (Or.inr (Or.inl hM12))
  · rcases Helpers.classification_of_five_transitive_of_card_eq_thirteen
        G X (by omega) h5 with hSym | hAlt
    · exact Or.inl hSym
    · exact Or.inr (Or.inl hAlt)

end FiveTransitive.LowDegreeClassification

end CFSG
