module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallComposeHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallSuzukiHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallDerivedHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallD4OrderHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallActorsHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallTableG2Holds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallTableTriD4Holds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallTableTwF4Holds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.S2MathAs51600Small

theorem smallTableInput_holds :
    SmallTableInput := by
  intro lab hlab hreg
  rcases hreg with h | h | h
  · exact smallTableG2_holds lab hlab h
  · exact smallTableTriD4_holds lab hlab h
  · exact smallTableTwF4_holds lab hlab h

theorem ggInnerOnD4Small_holds :
    GGInnerOnD4Small :=
  smallAssembly_holds
    (S2MathAs51600SmallCompose.smallVacuity_of_composition smallComposition_holds
      smallTableInput_holds smallInnerActorsInput_holds suzukiOrderInput_holds
      derivedOrderInput_holds d4OrderLowerInput_holds ggLabelRigidInput_holds
      S2MathAs51600.centralFixedComponentTransfer_holds)

end CFSG.StandardType.GGInnerD4SmallParts

end
