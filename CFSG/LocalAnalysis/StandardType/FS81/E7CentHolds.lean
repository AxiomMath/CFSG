module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentAssembly
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentControl
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentFlagTwo
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentHoltQuot
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentM
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentModelFlag
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentModelInv
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentModelM
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentModelP
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentModelSylow
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentSRoots
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentSix
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentSixLift
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogAssembly
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogIrr
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogRadical
public import CFSG.LocalAnalysis.StandardType.FS81.HoltSimpleControl
public import CFSG.LocalAnalysis.StandardType.FS81.D6Cent
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6Aut
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6Elt
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6Frame
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6Model
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6Torus

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem e7RootCentStep_holds :
    E7RootCentStep :=
  e7RootCentStep_of_pieces (fs81HoltQuot_of_holtSimpleControl holtSimpleControl_holds)
    fs81CentControl_holds
    (fs81CentM_of fs81FlagTwoGroup_holds (fs81SixLift_of_sixLemma fs81SixLemma_holds))
    e7CentModelSylow_holds e7CentModelQ_holds e7CentModelFlag_holds
    (e7CentModelJ_of e7CentSRoots_holds)
    (e7CentModelM_of e7CentSRoots_holds e7CentModelFlag_holds (e7CentModelJ_of e7CentSRoots_holds))
    e7CentModelK_holds e7CentModelP_holds e7CentModelInv_holds

theorem e7RootRecog_holds :
    E7RootRecog :=
  e7RootRecog_of_pieces holtSimpleControl_holds fs81RadicalOdd_holds fs81RootO2_holds
    e7ModelL3_holds e7ModelConj_holds (e7ModelO2_of_conj e7ModelConj_holds) e7ModelIrr_holds
    e7RootCentStep_holds

theorem l3RootFusionAt_D6_holds :
    L3RootFusionAt Row.D6 :=
  l3RootFusionAt_D6_of_recog
    (e7RootRecog_of_pieces holtSimpleControl_holds fs81RadicalOdd_holds fs81RootO2_holds
      e7ModelL3_holds e7ModelConj_holds (e7ModelO2_of_conj e7ModelConj_holds) e7ModelIrr_holds
      e7RootCentStep_holds)
    isEmSevenModel_holds
    (d6RootEltAt_of_rootLines e7TorusRootLines_holds (e8AutAt_D6_of_model isEmSevenModel_holds)
      (e8TorusAt_D6_of_model isEmSevenModel_holds))
    rowCentAt_D6 (e8TorusAt_D6_of_model isEmSevenModel_holds)
    (e8AutAt_D6_of_model isEmSevenModel_holds)

end CFSG.StandardType.FrameRoute.FS81
