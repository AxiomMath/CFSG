module

public import CFSG.Permutation.FiveTransitive.Degree36SixCases
public import CFSG.Permutation.FiveTransitive.Degree36SmallTwoFixerExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree36FourCases

open MulAction

theorem card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 128 ∨ Nat.card (fixingSubgroup P s) = 256 ∨
      Nat.card (fixingSubgroup P s) = 41472 ∨ Nat.card (fixingSubgroup P s) = 82944 := by
  rcases Degree36SixCases.card_cases P hcard h5 hnotAlt s hs with h2 | h4 | hrest
  · exact (Degree36SmallTwoFixerExclusion.excluded P hcard h5 hnotAlt s hs (Or.inl h2)).elim
  · exact (Degree36SmallTwoFixerExclusion.excluded P hcard h5 hnotAlt s hs (Or.inr h4)).elim
  · exact hrest

end FiveTransitive.Degree36FourCases

end CFSG
