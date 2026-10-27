module

public import CFSG.Permutation.FiveTransitive.TupleSemiregularFixedDegree
public import CFSG.Permutation.FiveTransitive.PermutationCardAlternating

public section

namespace CFSG

namespace FiveTransitive.ClassifiedOddSemiregularFive

open MulAction TupleSemiregularFour

theorem card_le_nine
    (X : Type*) [Fintype X] [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (h5 : IsMultiplyPretransitive P X 5) (hodd : Odd (Fintype.card X))
    (e : Fin 5 ↪ X) (S : Sylow 2 (stabilizer P e))
    (hfix : Nat.card (fixedPoints (image e S) X) = 5)
    (hfree : ∀ q : P, q ∈ image e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (image e S) X → q • x ≠ x)
    (hclass : Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Nat.card P = (Fintype.card X).factorial / 2) ∨
      (Fintype.card X = 12 ∧ Nat.card P = 95040) ∨
      (Fintype.card X = 24 ∧ Nat.card P = 244823040)) :
    Fintype.card X ≤ 9 := by
  have hcard : 5 ≤ Fintype.card X := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding e
  have hAlt : alternatingGroup X ≤ P := by
    apply PermutationCardAlternating.alternating_le_of_card X P (by omega)
    rcases hclass with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h.2
    · have ho := Nat.odd_iff.mp hodd
      omega
    · have ho := Nat.odd_iff.mp hodd
      omega
  exact TupleSemiregularFixedDegree.card_le_fixed_add_four X P 5 h5 hAlt e S hfix hfree

end FiveTransitive.ClassifiedOddSemiregularFive

end CFSG
