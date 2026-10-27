module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpE6
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpRankCls
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpRankExc
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTen
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpOmegaTen
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpUnitary
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTwelve
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpOmegaMinusTwelve
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan

public section

namespace CFSG.GGQ2Prime

theorem pumpUpLieInputs_of_open
    (hT : PumpUpTypeInput) (h2 : PumpUpTwistedE6Input) : PumpUpLieInputs where
  type := hT
  unitaryRank := pumpUpUnitaryRankInput_holds
  symplecticRank := pumpUpSymplecticRankInput_holds
  orthogonalRank := pumpUpOrthogonalRankInput_holds
  unitarySmall := pumpUpUnitarySmallInput_holds
  ten := pumpUpTenInput_holds
  omegaPlusTen := pumpUpOmegaPlusTenInput_holds
  twelve := pumpUpTwelveInput_holds
  omegaMinusTwelve := pumpUpOmegaMinusTwelveInput_holds
  e7 := pumpUpE7Input_holds
  e8 := pumpUpE8Input_holds
  e6 := pumpUpE6Input_of_twisted h2

end CFSG.GGQ2Prime

