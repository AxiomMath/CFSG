module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneHolds
public import CFSG.LocalAnalysis.StandardType.E6FieldNoneMixedFinal

public section

namespace CFSG.StandardType

theorem ggOuterInvAt_E6_of_centralizerG0 (h2 : GGO2CentralizerG0At .E6) : GGOuterInvAt .E6 :=
  ggOuterInvAt_E6_of_fieldNone h2 e6GraphNone_holds

theorem ggOuterInvModelDataAt_twistedE6_holds : GGOuterInvModelDataAt .twistedE6 :=
  ggOuterInvModelDataAt_twistedE6_of twistedE6GraphNone_holds

theorem ggOuterInvAt_twistedE6_of_centralizerG0 (h2 : GGO2CentralizerG0At .twistedE6) :
    GGOuterInvAt .twistedE6 :=
  ggOuterInvAt_twistedE6_of h2 twistedE6GraphNone_holds

end CFSG.StandardType
