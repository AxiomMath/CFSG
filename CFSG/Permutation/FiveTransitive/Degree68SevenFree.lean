module

public import CFSG.Permutation.FiveTransitive.Degree68SevenFiveFixed
public import CFSG.Permutation.FiveTransitive.Degree68FiveGlobal

public section

namespace CFSG

namespace FiveTransitive.Degree68SevenFree
open MulAction

theorem not_dvd_ambient
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 7 ∣ Nat.card P := by
  apply Degree68SevenFiveFixed.not_dvd_ambient_of_five_fixed_le P hcard h5 hnotAlt
  intro g hg
  exact (Degree68FiveGlobal.fixed_card_le_eight P hcard h5 hnotAlt g hg).trans (by decide)

end FiveTransitive.Degree68SevenFree

end CFSG
