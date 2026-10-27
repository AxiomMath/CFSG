module

public import CFSG.Permutation.FiveTransitive.Degree59ElevenContradiction

public section

namespace CFSG

namespace FiveTransitive.Degree59Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  exact Degree59ElevenContradiction.excluded P hcard h5 hnotAlt

end FiveTransitive.Degree59Classification

end CFSG
