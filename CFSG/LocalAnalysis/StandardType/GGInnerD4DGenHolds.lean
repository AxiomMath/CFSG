module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenSelectedHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenRepsHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenSupportedHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenComponentHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenCompositionHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenFixed
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.GGInnerD4DGenParts

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggInnerOnD4DGen_holds :
    GGInnerOnD4DGen :=
  dgenComposition_holds dgenSelectedMarking_holds
    S2MathAs51600DGenFixed.centralizerImageRewrite_holds orthogonalInnerRepresentatives_holds
    (orthogonalD4ComponentInner_of_supported supportedFixedThreeInner_holds)
    ggLabelRigidInput_holds S2MathAs51600.centralFixedComponentTransfer_holds

end CFSG.StandardType.GGInnerD4DGenParts

end
