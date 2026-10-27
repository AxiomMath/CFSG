module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestG2
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestON
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestJ3
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestMcL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem coverCenterThreeRest_of
    (hGA : GriessMultipliersAllModels) : CoverCenterThreeRest := by
  intro X _ _ hX hZ hS
  rcases hS with hG2 | hJ3 | hMcL | hON
  · exact card_center_dvd_three_of_G2 hGA hX hG2
  · exact card_center_dvd_three_of_J3 hX hZ hJ3.some
  · exact card_center_dvd_three_of_McL hX hZ hMcL.some
  · exact card_center_dvd_three_of_ON hX hZ hON.some

end CFSG.RankThree.PartTwo.Sec4.Census
