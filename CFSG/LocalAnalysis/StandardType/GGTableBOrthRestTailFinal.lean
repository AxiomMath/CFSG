module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailBstar

public section

namespace CFSG.StandardType

section Holds


theorem ggOrthRestTorusLiftInput_holds : GGOrthRestTorusLiftInput :=
  ggOrthRestTorusLiftInput_of_torus ggOrthRestCenterInput_holds ggOrthRestTorusInput_holds

theorem ggBstarInputOn_orthRest_of_bstarRest (ha₀ : GGLNoncyclicInput)
    (hB : GGOrthRestBstarRestInput) : GGBstarInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  ggBstarInputOn_orthRest ha₀ ggOrthRestTorusInput_holds hB

theorem ggBstarInputOn_orthRest_of_split (ha₀ : GGLNoncyclicInput)
    (hR : GGOrthRestMinusRankInput) (hO : GGOrthRestBstarOddInput)
    (hD : GGOrthRestBstarD4Input) : GGBstarInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  ggBstarInputOn_orthRest_of_bstarRest ha₀
    (ggOrthRestBstarRestInput_of_split ggOrthRestCenterInput_holds hR hO hD)

theorem ggStdSubPreInputOn_orthRest_of_endNode (ha₀ : GGLNoncyclicInput)
    (hE : GGOrthRestEndNodeInput) : GGStdSubPreInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  ggStdSubPreInputOn_orthRest ha₀ ggOrthRestTorusInput_holds hE

end Holds

end CFSG.StandardType
