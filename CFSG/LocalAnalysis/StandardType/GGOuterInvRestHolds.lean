module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtPSLFieldNoneHolds
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphCore
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphCore
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtFieldTagsHolds
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtOmega
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6GraphNone

public section

namespace CFSG.StandardType

theorem ggOuterInvRest_holds :
    GGOuterInvRest :=
  ⟨ggOuterInvAt_PSL_of (ggO2CentralizerG0At_holds .PSL) pslFieldNone_holds pslGraphNone_holds,
    ggOuterInvAt_PSU_of (ggO2CentralizerG0At_holds .PSU) psuGraphNone_holds,
    ggOuterInvAt_PSp, ggOuterInvAt_POmegaPlus, ggOuterInvAt_POmegaMinus, ggOuterInvAt_F4,
    ggOuterInvAt_E6_of_centralizerG0 (ggO2CentralizerG0At_holds .E6), ggOuterInvAt_E7,
    ggOuterInvAt_E8,
    ggOuterInvAt_twistedE6_of_centralizerG0 (ggO2CentralizerG0At_holds .twistedE6)⟩

theorem ggOTwoCentralizerInputStar_holds :
    GGOTwoCentralizerInputStar :=
  ggOTwoCentralizerInputStar_of_rest ggOuterInvRest_holds

end CFSG.StandardType
