module

public import CFSG.Permutation.FiveTransitive.SylowTwoFixedDegreeRefined
public import CFSG.Permutation.FiveTransitive.SmallDegreeClassification

public section

namespace CFSG

namespace FiveTransitive.SylowTwoFixedDegreeBounded

open MulAction
open FiveTransitive.SylowFixedActionCore

theorem fixed_degree_le_eight_or_eq_twelve
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) ≤ 8 ∨
      Nat.card (sylowFixedPoints X P s S) = 12 := by
  exact FiveTransitive.SylowTwoFixedDegreeRefined.fixed_degree_le_eight_or_eq_twelve_of_bounded_classification
    X P h5 s hs S FiveTransitive.SmallDegreeClassification.subgroup_card_classification

end FiveTransitive.SylowTwoFixedDegreeBounded

end CFSG
