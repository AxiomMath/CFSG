module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus

public section

namespace CFSG.StandardType

section Holds


theorem ggBstarInputOn_orthRest (ha₀ : GGLNoncyclicInput) (hT : GGOrthRestTorusInput)
    (hB : GGOrthRestBstarRestInput) : GGBstarInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  ggBstarInputOn_orthRest_of_inputs ha₀
    (ggOrthRestTorusLiftInput_of_torus ggOrthRestCenterInput_holds hT)
    (ggOrthRestBstarInput_of_rest ggOrthRestCenterInput_holds hB) ggOrthRestCenterInput_holds

theorem ggStdSubPreInputOn_orthRest (ha₀ : GGLNoncyclicInput) (hT : GGOrthRestTorusInput)
    (hE : GGOrthRestEndNodeInput) : GGStdSubPreInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  ggStdSubPreInputOn_orthRest_of_inputs ha₀
    (ggOrthRestTorusLiftInput_of_torus ggOrthRestCenterInput_holds hT) hE
    ggOrthRestCenterInput_holds

end Holds

end CFSG.StandardType
