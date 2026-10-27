module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeSecond

public section

namespace CFSG.StandardType

namespace TriBridge

set_option linter.unusedSectionVars false

theorem ggD4GraphFieldLayerInput_holds : GGD4GraphFieldLayerInput :=
  ggD4GraphFieldLayerInput_of_lang ggD4GraphFieldLangInput_holds
    ggD4GraphFieldFixQuasisimpleInput_holds

theorem ggD4GraphLayerInput_holds : GGD4GraphLayerInput :=
  ggD4GraphLayerInput_of_pgl ggD4GraphClassPGLInput_holds ggD4GraphFixQuasisimpleInput_holds

end TriBridge

end CFSG.StandardType
