module

public import CFSG.RankThree.PartOne.KF.R1Layer
public import CFSG.RankThree.PartOne.KLAY.Row2
public import CFSG.RankThree.PartOne.KLAY.Row3
public import CFSG.RankThree.PartOne.KLAY.Row4
public import CFSG.RankThree.PartOne.KF.R5Layer
public import CFSG.RankThree.PartOne.KF.R6Layer
public import CFSG.RankThree.PartOne.KF.R7Layer
public import CFSG.RankThree.PartOne.KF.R8Layer
public import CFSG.RankThree.PartOne.KF.R9Layer
public import CFSG.RankThree.PartOne.KEXC.Layer10
public import CFSG.RankThree.PartOne.KFOUT3.L12Layer
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.RankThree.PartOne.HNB.RowModelsDistinct

public section

namespace CFSG.RankThree.PartOne

theorem kf1212Layer_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF1212Layer := by
  refine kf1212Layer_of_rows TCB.schreierFor_inCatalog_holds HNB.rowModelsDistinct_holds ?_
  intro r h1 h12 h11
  interval_cases r
  · exact kf1212LayerRow1
  · exact KLAY.kf1212LayerRow2
  · exact KLAY.kf1212LayerRow3
  · exact KLAY.kf1212LayerRow4
  · exact kf1212LayerRow5
  · exact kf1212LayerRow6
  · exact kf1212LayerRow7
  · exact kf1212LayerRow8
  · exact kf1212LayerRow9 (psuFourEvenCenterTrivial_of_multipliers hGA)
  · exact KEXC.kf1212LayerRow10
  · exact absurd rfl h11
  · exact kf1212LayerRow12

end CFSG.RankThree.PartOne
