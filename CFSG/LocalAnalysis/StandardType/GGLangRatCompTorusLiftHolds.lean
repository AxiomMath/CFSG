module

public import CFSG.LocalAnalysis.StandardType.GGLangRatLatticeLiftHolds
public import CFSG.LocalAnalysis.StandardType.GGLangRatRoutes

public section

namespace CFSG.StandardType.LangRat

theorem langRatCompTorusLift_holds :
    LangRatCompTorusLift :=
  langRatCompTorusLift_of_lift_fixed langRatLatticeLift_holds langRatTorusFixedMem_holds

theorem langRatCompInnerAct_holds :
    LangRatCompInnerAct :=
  langRatCompInnerAct_of_torusLift langRatCompTorusLift_holds

end CFSG.StandardType.LangRat
