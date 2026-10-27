module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveQ2PrimeLDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeNamed

public section

namespace CFSG.StandardType

theorem ggSecFiveQ2PrimeLInput_of_named (hL : GGLBalanceInput) (hI : GGQ2Prime.PumpUpLieInputs)
    (hW : GGQ2Prime.WeylCoordInput) (h81 : GGQ2Prime.Lemma81Input)
    (hc : GGQ2Prime.Lemma101cInput) (hk : GGQ2Prime.Lemma1025Input) (hF : GGQ2Prime.F14Input) :
    GGSecFiveQ2PrimeLInput := by
  intro G _ _ B Bs x L D J 𝒦 hcfg hcard hm hWA hAL
  exact GGQ2Prime.q2p_of_named hL hI hW h81 hc hk hF hcfg hcard hm hWA hAL

end CFSG.StandardType
