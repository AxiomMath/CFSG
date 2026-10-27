module

public import CFSG.Permutation.FiveTransitive.Degree60ThreeBoundCore
public import CFSG.Permutation.FiveTransitive.Degree60FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeBound

open MulAction SylowFixedActionCore

theorem card_le_243
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S ≤ 243 := by
  exact Degree60ThreeBoundCore.card_le_243_of_five_fixed_cases P hcard h5 hnotAlt
    (Degree60FiveOrder.fixed_card_cases P hcard h5 hnotAlt) s hs S

end FiveTransitive.Degree60ThreeBound

end CFSG
