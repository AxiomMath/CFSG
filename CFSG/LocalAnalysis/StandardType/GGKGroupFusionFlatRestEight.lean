module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKHolds
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestAlt
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestOuter
import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlatMarking

public section

namespace CFSG.StandardType

@[expose] def GGKGroupFusionRest8FlatK : Prop :=
  GGLieParabolicCharInput ∧ GGD4FieldAutMaximalInput ∧ GGKGroupFusionAtFlatK GGKFSporadic

end CFSG.StandardType
