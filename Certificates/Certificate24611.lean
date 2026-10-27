module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutECore
import Certificates.Kernel.Fin76bOm.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b in
theorem certificate24611 : ∃ ht : CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9) ∈ j3P,
    AutEFact ↥(CFSG.EvenSporadicStandard.Fin76b.rootGroup ↥j3P ⟨CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9), ht⟩) :=
  KernelC24608.j3_autEFact_t0

end Certificates
