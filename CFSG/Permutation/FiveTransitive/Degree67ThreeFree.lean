module

public import CFSG.Permutation.FiveTransitive.Degree67ThreeConditional
public import CFSG.Permutation.FiveTransitive.Degree67SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree67ThreeFree

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree67ThreeConditional.not_dvd_five_fixer_of_seven_fixed_four
    P hcard h5 hnotAlt (Degree67SevenFree.fixed_card_eq_four P hcard h5 hnotAlt) s hs

end FiveTransitive.Degree67ThreeFree

end CFSG
