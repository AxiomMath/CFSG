module

public import CFSG.Permutation.FiveTransitive.Degree72FactorizationConstraints

public section

namespace CFSG

namespace FiveTransitive.Degree72Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  exact Degree72FactorizationConstraints.excluded P hcard h5 hnotAlt

end FiveTransitive.Degree72Classification

end CFSG
