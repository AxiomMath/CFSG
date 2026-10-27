module

public import CFSG.Permutation.FiveTransitive.Degree59SevenFixedThree
public import CFSG.Permutation.FiveTransitive.Degree59FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree59SevenFree

open MulAction

theorem fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 7) : Nat.card (Function.fixedPoints g.val) = 3 := by
  exact Degree59SevenFixedThree.fixed_card_eq_three_of_five_fixed_cases
    P hcard h5 hnotAlt (Degree59FiveOrder.fixed_card_cases P hcard h5 hnotAlt) g hg

end FiveTransitive.Degree59SevenFree

end CFSG
