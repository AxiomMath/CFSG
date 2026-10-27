module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTriality
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityEight

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.Triality

theorem ggOrdPTrialityInput_of_graph_layers (hF : GGOrdPFieldConjAt .POmegaPlus)
    (hGF : GGD4GraphFieldLayerInput) (hG : GGD4GraphLayerInput) : GGOrdPTrialityInput :=
  ggOrdPTrialityInput_of_graph hF hGF hG OrdPTri.ggD4ThreeCentralizerEightInput_holds

theorem ggOrdPTrialityInput_of_rest_layers (hF : GGOrdPFieldConjPOmegaPlusRest)
    (hGF : GGD4GraphFieldLayerInput) (hG : GGD4GraphLayerInput) : GGOrdPTrialityInput :=
  ggOrdPTrialityInput_of_rest hF hGF hG OrdPTri.ggD4ThreeCentralizerEightInput_holds

end CFSG.StandardType
