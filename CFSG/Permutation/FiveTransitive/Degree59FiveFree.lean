module

public import CFSG.Permutation.FiveTransitive.Degree59FiveFreeCore
public import CFSG.Permutation.FiveTransitive.Degree59SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree59FiveFree

open MulAction

theorem fixed_card_eq_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 4 := by
  exact Degree59FiveFreeCore.fixed_card_eq_four_of_seven_fixed_three P hcard h5 hnotAlt
    (Degree59SevenFree.fixed_card_eq_three P hcard h5 hnotAlt) g hg

end FiveTransitive.Degree59FiveFree

end CFSG
