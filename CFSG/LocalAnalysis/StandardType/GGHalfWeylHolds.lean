module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylInput
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGHalfStageA
public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes

public section

namespace CFSG.StandardType

theorem ggTypeAHalfLeviInput_holds : GGTypeAHalfLeviInput :=
  ggTypeAHalfLeviInput_of_torusFrame (@ggHalf_torusFrame)

theorem ggTypeAHalfCoordInput_of_subcomponent (hsub : GGNbrSubcomponentInput) :
    GGTypeAHalfCoordInput :=
  ggTypeAHalfCoord_of_levi hsub ggTypeAHalfLeviInput_holds

theorem ggTypeAHalfJoinEndNodes_of_subcomponent_five (hsub : GGNbrSubcomponentInput)
    (h5 : GGHalfEndNodesOn (fun n => n = 5)) : GGTypeAHalfJoinEndNodesInput :=
  ggTypeAHalfJoinEndNodes_of_coord_five (ggTypeAHalfCoordInput_of_subcomponent hsub) h5

end CFSG.StandardType

end
