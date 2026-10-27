module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourCount
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourD4

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.GGFinModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem rckExcShapeFour_holds :
    RCKExcShapeFour := by
  intro p hp hp2 a hpa ha1 ρ hroot hneg hform hsq hstab i hshape
  rcases hshape with ⟨hr48, h48⟩ | ⟨hr72, h72⟩ | ⟨-, h126⟩ | ⟨-, h240⟩ | ⟨hr4, h24, hni⟩
  · exact rckExc_not_shape_F4 hp hp2 hpa i ⟨hr48, h48⟩
  · exact rckExc_not_shape_E6 hp hp2 hpa hroot hneg hform hsq hstab i ⟨hr72, h72⟩
  · exact rck_ncard_ne_126 hroot hneg hform hsq hstab i h126
  · exact rck_ncard_ne_240 ha1 i h240
  · exact rckExc_not_shape_D4 hp hp2 hpa hroot hneg hform hsq hstab i ⟨hr4, h24, hni⟩

end CFSG.StandardType.RCKRP
