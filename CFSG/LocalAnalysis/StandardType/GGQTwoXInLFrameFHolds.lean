module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameF
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds

public section

namespace CFSG.StandardType

theorem ggQTwoXInL_frame_formed :
    GGQTwoXInLFrameFormed :=
  ggQTwoXInL_frame_formed_of TCJ.ggTCJKnown_holds ggLabelRigidInput_holds
    (ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)

end CFSG.StandardType

end
