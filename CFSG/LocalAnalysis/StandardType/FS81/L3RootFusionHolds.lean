module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentHolds
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8
public import CFSG.LocalAnalysis.StandardType.FS81.RootTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutE7
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit
public import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
public import CFSG.LocalAnalysis.StandardType.FS81.S7BetaCent
public import CFSG.LocalAnalysis.StandardType.FS81.S7BetaTor
public import CFSG.LocalAnalysis.StandardType.FS81.S7InvComm
public import CFSG.LocalAnalysis.StandardType.FS81.S7RadicalE7
public import CFSG.LocalAnalysis.StandardType.FS81.S7RadicalTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.S7RootCent
public import CFSG.LocalAnalysis.StandardType.FS81.S7TorusAt
public import CFSG.Holt.CaseTwoBW
public import CFSG.Holt.General.Basic
public import CFSG.Holt.General.ComponentsImage
public import CFSG.Holt.General.OddOrbits
public import CFSG.Holt.OddCoreTwoGroupBasic
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem l3RootFusionAt_E7_holds :
    L3RootFusionAt Row.E7 :=
  l3RootFusionAt_E7_of rowCentAt_E7 e8RadicalAt_E7 e8AutAt_E7 e8TorusAt_E7 e8InvCommAt_E7
    (e8RootCentAt_E7_of_recog e7RootRecog_holds)

theorem l3RootFusionAt_twD7_holds :
    L3RootFusionAt Row.twD7 :=
  l3RootFusionAt_twD7_of rowCentAt_twD7 e8RadicalAt_twD7 e8AutAt_twD7 e8TorusAt_twD7
    e8InvCommAt_twD7 (e8RootCentAt_twD7_of_recog e7RootRecog_holds)
    (twD7BetaCentAt_of_recog e7RootRecog_holds) twD7BetaTorAt_holds

theorem l3RootFusion_holds :
    L3RootFusion :=
  l3RootFusion_of_rows l3RootFusionAt_D6_holds l3RootFusionAt_twD7_holds l3RootFusionAt_E7_holds

end CFSG.StandardType.FrameRoute.FS81

end
