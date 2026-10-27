module

public import CFSG.Permutation.FiveTransitive.Degree58SevenFixedTwo
public import CFSG.Permutation.FiveTransitive.Degree58FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree58SevenFree

open MulAction

theorem fixed_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 7) : Nat.card (Function.fixedPoints g.val) = 2 := by
  exact Degree58SevenFixedTwo.fixed_card_eq_two_of_five_fixed_cases
    P hcard h5 hnotAlt (Degree58FiveOrder.fixed_card_cases P hcard h5 hnotAlt) g hg

end FiveTransitive.Degree58SevenFree

end CFSG
