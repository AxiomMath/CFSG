module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c1610_commutator_of_isL3 {Y : Type} [Group Y] [Finite Y] (h : IsL3 Y 1) :
    _root_.commutator Y = ⊤ := by
  haveI : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator Y) with hc | hc
  · exfalso
    have hz : Subgroup.center Y = ⊤ := (commutator_eq_bot_iff_center_eq_top Y).1 hc
    rw [center_eq_bot_of_isL3 h] at hz
    exact bot_ne_top hz
  · exact hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
