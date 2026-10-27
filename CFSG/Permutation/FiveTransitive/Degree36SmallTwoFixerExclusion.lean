module

public import CFSG.Permutation.FiveTransitive.Degree36SmallTwoFixerData
public import CFSG.Permutation.FiveTransitive.Degree36SmallTwoCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree36SmallTwoFixerExclusion

open MulAction FixedNormalizerAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (_hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hH : Nat.card (fixingSubgroup P s) = 2 ∨ Nat.card (fixingSubgroup P s) = 4) : False := by
  have hQ := Degree36SmallTwoFixerData.is_two_group (fixingSubgroup P s) hH
  have hF := Degree36SmallTwoFixerData.fixed_card_cases P hcard h5 s hs hH
  rw [fixed_eq] at hF
  have h9 := Degree36SmallTwoFixerData.nine_dvd_centralizer P hcard h5 s hs hH
  exact Degree36SmallTwoCentralizer.nine_not_dvd_centralizer P hcard (fixingSubgroup P s)
    hQ hF (Degree36SmallTwoFixerData.order_three_fixed_cases P hcard h5 s hs hH) h9

end FiveTransitive.Degree36SmallTwoFixerExclusion

end CFSG
