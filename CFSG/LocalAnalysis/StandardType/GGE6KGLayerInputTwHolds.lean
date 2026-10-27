module

public import CFSG.LocalAnalysis.StandardType.GGKGTwGlue
public import CFSG.LocalAnalysis.StandardType.GGTwE6A3LayerHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4LayerHolds

public section

namespace CFSG.StandardType


theorem ggE6KGLayerInputTw_holds : GGE6KGLayerInputTw :=
  ggE6KGLayerInputTw_of_layers KGL.ggTwE6D4LayerInput_holds KGL.ggTwE6A3LayerInput_holds

end CFSG.StandardType

end
