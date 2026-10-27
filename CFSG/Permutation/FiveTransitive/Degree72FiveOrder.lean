module

public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenOrder
public import CFSG.Permutation.FiveTransitive.Degree72FiveTwelveOrder
public import CFSG.Permutation.FiveTransitive.Degree72FiveFixedCases

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveOrder
open MulAction SylowFixedActionCore

theorem card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S ≤ 5 := by
  by_cases hS : Nat.card S = 1
  · omega
  rcases Degree72FiveFixedCases.five_fixed_card_cases P hcard h5 hnotAlt s hs S hS with hF | hF
  · exact Degree72FiveSevenOrder.sylow_card_le_five P hcard h5 hnotAlt s hs S hF
  · exact Degree72FiveTwelveOrder.sylow_card_le_five P hcard h5 hnotAlt s hs S hF

end FiveTransitive.Degree72FiveOrder

end CFSG
