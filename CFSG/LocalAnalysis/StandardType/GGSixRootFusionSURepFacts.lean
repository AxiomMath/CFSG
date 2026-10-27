module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsH
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsK

public section

namespace CFSG.StandardType

open SUFacts

theorem ggSUSixAlphaInput_holds : GGSUSixAlphaInput :=
  ggSUSixAlphaInput_of_sides ggSUSixHSideInput_holds ggSUSixKSideInput_holds

end CFSG.StandardType
