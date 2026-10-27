module

public import CFSG.Permutation.FiveTransitive.Degree58ElevenContradiction

public section

namespace CFSG

namespace FiveTransitive.Degree58Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  exact Degree58ElevenContradiction.excluded P hcard h5 hnotAlt

end FiveTransitive.Degree58Classification

end CFSG
