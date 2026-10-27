module

public import CFSG.Permutation.FiveTransitive.Degree53FiveFreeCore
public import CFSG.Permutation.FiveTransitive.Degree53SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree53FiveFree

open MulAction

theorem fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 3 := by
  exact Degree53FiveFreeCore.fixed_card_eq_three_of_seven_fixed_four P hcard h5 hnotAlt
    (Degree53SevenFree.fixed_card_eq_four P hcard h5 hnotAlt) g hg

end FiveTransitive.Degree53FiveFree

end CFSG
