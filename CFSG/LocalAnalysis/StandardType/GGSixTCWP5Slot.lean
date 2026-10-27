module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvdJ
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Assembly
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4AssemblyE
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UF4Small
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Leaves
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaTC

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType

theorem ggSixFieldExtTableCRemainingRes_of_inputs
    (hnc : GGLNoncyclicInput) (h64 : GGSixCentreOddInput) (hP : GGStdSubPrimeInput)
    (hPSp : GGSixFieldExtTableCAt .PSp)
    (hR : LangFamilyCompFieldSL) (hL : LangFamilyCompLabel) (hG : GGTCInputG6InnerDiagLang)
    (hGTw : GGTCInputG6InnerDiagLangTw) (hRC0 : LangNontoralCompField)
    (hA : TwE6q2OrderThreeCentralizers) (hF4 : LangFamilyCompFieldF4Data) :
    GGSixFieldExtTableCRemainingRes :=
  ⟨ggSixFieldExtTableCAt_of_tcAt ggTCAt_PSL, ggSixFieldExtTableCAt_of_tcAt ggTCAt_PSU, hPSp,
    ggSixFieldExtTableCAt_of_known hnc h64 hP ggSixTCKnown_POmegaPlus,
    ggSixFieldExtTableCAt_of_known hnc h64 hP ggSixTCKnown_POmegaMinus,
    ggSixFieldExtTableCAt_of_tcAt (ggTCAt_F4_of_fieldData hF4),
    ggSixFieldExtTableCAt_of_tcAt (ggTCAt_E6_of_inputs hR hL hG),
    ggSixFieldExtTableCAt_of_tcAt (ggTCAt_E7_of_inputs hR),
    ggSixFieldExtTableCAt_of_tcAt (ggTCAt_E8_of_inputs hR hL hG),
    ggSixFieldExtTableCTwistedE6Res_of_tcLe (ggTCTwE6AtLe_of_inputs hR hL hGTw hRC0 hA)⟩

end CFSG.StandardType.TableCRes

end
