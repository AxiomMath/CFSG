module

public import CFSG.Permutation.FiveTransitive.Degree69SevenFiveFixed
public import CFSG.Permutation.FiveTransitive.Degree69FiveGlobal

public section

namespace CFSG

namespace FiveTransitive.Degree69SevenFree
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  apply Degree69SevenFiveFixed.not_dvd_five_fixer_of_five_fixed_le P hcard h5 hnotAlt _ s hs
  intro g hg
  exact (Degree69FiveGlobal.fixed_card_le_nine P hcard h5 hnotAlt g hg).trans (by decide)

theorem not_dvd_ambient
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 7 ∣ Nat.card P := by
  apply Degree69SevenFiveFixed.not_dvd_ambient_of_five_fixed_le P hcard h5 hnotAlt
  intro g hg
  exact (Degree69FiveGlobal.fixed_card_le_nine P hcard h5 hnotAlt g hg).trans (by decide)

end FiveTransitive.Degree69SevenFree

end CFSG
