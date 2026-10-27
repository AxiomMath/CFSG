module

public import CFSG.LocalAnalysis.StandardType.GGPumpUpType
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveQ2PrimeLPumpUpOpen
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL101c
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF14
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeWeylCoords
public import CFSG.LocalAnalysis.StandardType.GGSecFiveQ2PrimeL
public import Certificates.Certificate3600
public import Certificates.Certificate3920

public section

namespace CFSG.GGQ2Prime

theorem pumpUpLieInputs_holds
    : PumpUpLieInputs :=
  pumpUpLieInputs_of_open pumpUpTypeInput_holds pumpUpTwistedE6Input_holds

end CFSG.GGQ2Prime

namespace CFSG.StandardType

theorem ggSecFiveQ2PrimeLInput_of_balance_81
    (hL : GGLBalanceInput) (h81 : GGQ2Prime.Lemma81Input) : GGSecFiveQ2PrimeLInput :=
  ggSecFiveQ2PrimeLInput_of_named hL GGQ2Prime.pumpUpLieInputs_holds
    GGQ2Prime.weylCoordInput_holds h81 GGQ2Prime.lemma101cInput_holds
    (GGQ2Prime.lemma1025Input_of_lemma101cInput GGQ2Prime.lemma101cInput_holds)
    GGQ2Prime.f14Input_holds

end CFSG.StandardType

end
