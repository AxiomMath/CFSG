module

public import CFSG.Permutation.FiveTransitive.Degree58ThreeConditional
public import CFSG.Permutation.FiveTransitive.Degree58SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree58ThreeFree

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree58ThreeConditional.not_dvd_five_fixer_of_seven_fixed_two
    P hcard h5 hnotAlt (Degree58SevenFree.fixed_card_eq_two P hcard h5 hnotAlt) s hs

end FiveTransitive.Degree58ThreeFree

end CFSG
