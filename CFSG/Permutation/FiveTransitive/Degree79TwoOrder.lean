module

public import CFSG.Permutation.FiveTransitive.Degree79TwoFiveOrder
public import CFSG.Permutation.FiveTransitive.Degree79TwoSevenBound

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoOrder
open MulAction SylowFixedActionCore

theorem card_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S ≤ 2^22 := by
  rcases Degree79TwoEntrance.fixed_card_cases P hcard h5 s hs S with hF | hF
  · exact Degree79TwoFiveOrder.card_le P hcard h5 hnotAlt s hs S hF
  have hseven := Degree79SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt
  have hthree := Degree79ThreeFreeFromSeven.not_dvd_five_fixer P hcard h5 hnotAlt hseven
  have hb := Degree79TwoSevenBound.sylow_card_le_eight P hcard h5 hnotAlt hthree
    (Degree79FiveFree.not_dvd_five_fixer P hcard h5 hnotAlt) hseven s hs S hF
  exact hb.trans (by norm_num)

end FiveTransitive.Degree79TwoOrder

end CFSG
