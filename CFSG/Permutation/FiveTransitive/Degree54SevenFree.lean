module

public import CFSG.Permutation.FiveTransitive.Degree54SevenConditional
public import CFSG.Permutation.FiveTransitive.Degree54FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree54SevenFree

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree54SevenConditional.not_dvd_five_fixer_of_five_fixed_four
    P hcard h5 hnotAlt (Degree54FiveFree.fixed_card_eq_four P hcard h5 hnotAlt) s hs

theorem not_dvd_ambient
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 7 ∣ Nat.card P := by
  exact Degree54SevenConditional.not_dvd_ambient_of_five_fixed_four
    P hcard h5 hnotAlt (Degree54FiveFree.fixed_card_eq_four P hcard h5 hnotAlt)

end FiveTransitive.Degree54SevenFree

end CFSG
