module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155NoG28
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.RankThree.PartOne.N143.T2LargeAll
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Route
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Setup
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90J2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem step155NoG28WR_of_res3
    (h134 : Item134) (h135 : Item135) (h41p : Sec4.Item4_1LargePrime)
    (h41c : Sec4.Item4_1ThreeCover) (h41a : Sec4.Item4_1LargeAll) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hspor : SporadicModels131) (hK9 : Res3K9)
    (hND : Res3NoDatum) : Step155NoG28WR := by
  intro G _ _ A c L hR h3 hJ _ X K' Y M T P hC _ _ _ _ _ _ g hg hgZ hodd hCV
  obtain ⟨d, K, h⟩ := exists_res3Ctx h134 h48 hR hJ h3
  exact h.eq_one_of_noDatum hND h415 hspor h41p h41a
    (h.theorem90 h45 h48 h41p h41c h135 Thm90.j2Facts_native hK9) hC hg hgZ hodd hCV

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
