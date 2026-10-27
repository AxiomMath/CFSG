module

public import CFSG.Permutation.FiveTransitive.LowDegreeClassification
public import CFSG.Permutation.FiveTransitive.Degree14
public import CFSG.Permutation.FiveTransitive.Degree16Classification
public import CFSG.Permutation.FiveTransitive.Degree17
public import CFSG.Permutation.FiveTransitive.Degree18

public section

namespace CFSG

namespace FiveTransitive.ThroughEighteenClassification

theorem faithful_action_card_classification
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hlower : 5 ≤ Fintype.card X) (hupper : Fintype.card X ≤ 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    let n := Fintype.card X
    Fintype.card G = n.factorial ∨
      (7 ≤ n ∧ Fintype.card G = n.factorial / 2) ∨
      (n = 12 ∧ Fintype.card G = 95040) ∨
      (n = 24 ∧ Fintype.card G = 244823040) := by
  classical
  by_cases hlow : Fintype.card X ≤ 13
  · exact LowDegreeClassification.classification_of_five_transitive_of_card_le_thirteen
      G X hlower hlow h5
  have hcases : Fintype.card X = 14 ∨ Fintype.card X = 15 ∨
      Fintype.card X = 16 ∨ Fintype.card X = 17 ∨ Fintype.card X = 18 := by omega
  suffices h : Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Fintype.card G = (Fintype.card X).factorial / 2) from
    h.imp_right Or.inl
  rcases hcases with h14 | h15 | h16 | h17 | h18
  · exact Degree14.classification_of_five_transitive_of_card_eq_fourteen G X h14 h5
  · exact Degree15.classification_of_five_transitive_of_card_eq_fifteen G X h15 h5
  · exact Degree16.classification_of_five_transitive_of_card_eq_sixteen G X h16 h5
  · exact Degree17.classification_of_five_transitive_of_card_eq_seventeen G X h17 h5
  · exact Degree18.classification_of_five_transitive_of_card_eq_eighteen G X h18 h5

end FiveTransitive.ThroughEighteenClassification

end CFSG
