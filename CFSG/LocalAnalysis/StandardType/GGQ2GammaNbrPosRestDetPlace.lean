module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcCert
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Frame
public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Gamma
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtD5Bridge
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtPlane
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtUnitFull
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtUnitHeart
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSmall
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem ggQ2GammaNbrPosRestDetInput_of_placements
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput)
    (hplCl : PlacementInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplEx : PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQ2GammaNbrPosRestDetInput :=
  ggQ2GammaNbrPosRestDet_of_cover
    (ggQ2ExtCoverInput_of_statements hLB hP ggLabelRigidInput_holds extD5Bridge_holds hplCl hplEx
      (placementInputOn_small _) extCasesLin_holds extCasesSymp_holds extCasesOrth_holds
      extCasesUnitFull_holds extCasesUnitHeart_holds ExcRaw.extCases_excRaw)
    (ggQ2NbrD5Gamma_holds hLB hP h5)

end CFSG.StandardType

end
