module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift
import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLiftHolds
import CFSG.LocalAnalysis.StandardType.GGLangRatCompFieldLen

public section

namespace CFSG.StandardType.LangRat

theorem langRatCompKillsP_holds
    : LangRatCompKillsP :=
  langRatCompKillsP_of_torusLift langRatCompTorusLift_holds langRatCompFieldLen_holds

end CFSG.StandardType.LangRat
