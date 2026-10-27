module

public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenFree
public import CFSG.Permutation.FiveTransitive.Degree72FiveRefinedGlobal

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveActual
open MulAction SylowFixedActionCore

theorem fixed_card_eq_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : Nat.card (sylowFixedPoints X P s S) = 12 := by
  exact Degree72FiveRefined.fixed_card_eq_twelve P hcard h5 hnotAlt
    (Degree72FiveSevenFree.fixed_card_eq_two P hcard h5 hnotAlt) s hs S hS

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) :
    Nat.card (Function.fixedPoints g.val) = 2 ∨ Nat.card (Function.fixedPoints g.val) = 12 := by
  exact Degree72FiveRefinedGlobal.fixed_card_cases P hcard h5 hnotAlt
    (Degree72FiveSevenFree.fixed_card_eq_two P hcard h5 hnotAlt) g hg

end FiveTransitive.Degree72FiveActual

end CFSG
