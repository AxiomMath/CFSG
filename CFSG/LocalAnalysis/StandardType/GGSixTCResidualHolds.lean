module

public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualU62Facts
public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualOutLift

public section

namespace CFSG.StandardType

open CFSG.StandardType.TCResidual

section KnownLie

theorem ggSixTCResidualExcluded_holds : GGSixTCResidualExcluded :=
  ggSixTCResidualExcluded_of_facts (fun _ _ _ _ hperf hodd hmod => ggU62_facts hperf hodd hmod)
    (fun _ _ _ _ hperf hmod => ggU62_out hperf hmod)

end KnownLie

end CFSG.StandardType

end
