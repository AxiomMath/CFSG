module

public import CFSG.Permutation.FiveTransitive.Degree29ThirteenEntrance

public section

namespace CFSG

namespace FiveTransitive.Degree29Classification

open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  exact Degree29ThirteenEntrance.excluded P hcard h5 hnotAlt

theorem subgroup_card_classification
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) :
    Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Nat.card P = (Fintype.card X).factorial / 2) := by
  rcases FiveTransitive.alt_le_perm_card_dichotomy X P (by omega)
    (alternatingGroup_le P hcard h5) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by omega,h⟩

end FiveTransitive.Degree29Classification

end CFSG
