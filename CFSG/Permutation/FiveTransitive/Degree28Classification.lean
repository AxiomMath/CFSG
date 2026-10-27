module

public import CFSG.Permutation.FiveTransitive.Degree28SmallFixerExclusion
public import CFSG.Permutation.FiveTransitive.Degree28ThirteenReduction

public section

namespace CFSG

namespace FiveTransitive.Degree28Classification

open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by simp [Set.ncard_univ,hcard])
  have hc := Degree28ThirteenReduction.five_fixer_card P hcard h5 hnotAlt s hs
  exact Degree28SmallFixerExclusion.contradiction P hcard h5 hnotAlt s hs (by omega)

theorem subgroup_card_classification
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) :
    Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Nat.card P = (Fintype.card X).factorial / 2) := by
  rcases FiveTransitive.alt_le_perm_card_dichotomy X P (by omega)
    (alternatingGroup_le P hcard h5) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by omega,h⟩

end FiveTransitive.Degree28Classification

end CFSG
