
module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
import Certificates.Kernel.Fin76bOm.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b in
theorem certificate24609 : ∃ ht : CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9) ∈ j3P, RootFactsFor ↥j3P ⟨CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9), ht⟩ :=
  KernelC24608.j3_rootFactsFor_t0

end Certificates
