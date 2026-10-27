module

public import CFSG.Permutation.FiveTransitive.Degree79TwoOrder
public import CFSG.Permutation.FiveTransitive.Degree79OrderContradiction

public section

namespace CFSG

namespace FiveTransitive.Degree79Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  exact Degree79OrderContradiction.excluded P hcard h5 hnotAlt
    (Degree79TwoOrder.card_le P hcard h5 hnotAlt)

end FiveTransitive.Degree79Classification

end CFSG
