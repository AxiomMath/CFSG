module

public import CFSG.Permutation.FiveTransitive.Degree80TwoSixBound
public import CFSG.Permutation.FiveTransitive.Degree80TwoResidual

public section

namespace CFSG

namespace FiveTransitive.Degree80Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  apply Degree80TwoResidual.excluded_of_six_bound P hcard h5 hnotAlt
  intro s hs S hF
  exact (Degree80TwoSixBound.sylow_card_le_eight P hcard h5 hnotAlt s hs S hF).trans (by decide)

end FiveTransitive.Degree80Classification

end CFSG
