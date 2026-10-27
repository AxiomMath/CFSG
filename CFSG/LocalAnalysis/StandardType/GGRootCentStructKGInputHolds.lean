module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructAll
import CFSG.LocalAnalysis.StandardType.GGSixStepOneSchreier
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

theorem ggRootCentStructKGInput_holds : GGRootCentStructKGInput :=
  ggRootCentStructKGInput_of_schreierPerfect
    (ggSchreierPerfectInput_of_lieSchreier
      (ggLieSchreierInput_of_schreierFor CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds))

end CFSG.StandardType

end
