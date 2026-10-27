module

public import CFSG.Permutation.FiveTransitive.Degree79ThreeConditional
public import CFSG.Permutation.FiveTransitive.Degree79SevenFreeFixity

public section

namespace CFSG

namespace FiveTransitive.Degree79ThreeFreeFromSeven
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ t : Set X, t.ncard = 5 → ¬ 7 ∣ Nat.card (fixingSubgroup P t))
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree79ThreeConditional.not_dvd_five_fixer_of_seven_fixed_two
    P hcard h5 hnotAlt (Degree79SevenFreeFixity.fixed_card_eq_two P hcard hseven) s hs

end FiveTransitive.Degree79ThreeFreeFromSeven

end CFSG
