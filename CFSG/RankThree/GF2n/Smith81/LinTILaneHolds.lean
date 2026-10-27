module

public import CFSG.RankThree.GF2n.Smith81.Sec2Induction
public import CFSG.RankThree.GF2n.Smith81.KG2Holds
public import CFSG.RankThree.GF2n.Smith81.InspAllK
import CFSG.RankThree.GF2n.Smith81.Identify
import CFSG.RankThree.GF2n.Smith81.Lin3Holds
import CFSG.RankThree.GF2n.Smith81.Lin216E6
import CFSG.RankThree.GF2n.Smith81.TiBridge
import CFSG.RankThree.GF2n.Smith81.TiD2Fusion
import CFSG.RankThree.GF2n.Smith81.TiD3ModuleProof
import CFSG.RankThree.GF2n.Smith81.TiD3Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.Insp


theorem smithLaneLin_holds : LaneLinStep :=
  smithLaneLin_of_inputs timmesfeldOutcomeStatement_of_outcome lin3Statement_holds
    linRootClass_holds linInspect_holds linTIIdentify_holds

theorem tiLinearD2_holds : TiLinearD2Step :=
  tiLinearD2_of_inputs timmesfeldOutcomeStatement_of_outcome lin3Statement_holds
    linRootClass_holds linInspect_holds linTIIdentify_holds

theorem laneTIStep_holds : LaneTIStep :=
  laneTIStep_of_inputs corBRankTwo_holds tiLieOrders_holds tiFusionD2
      (tiFusionD3_of_module d3ModuleStatement_holds) tiLinearD2_holds

end CFSG.RankThree.GF2n.Smith81
