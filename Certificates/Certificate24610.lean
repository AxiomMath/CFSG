module

public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutECore
import Certificates.Kernel.Fin76bOm.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b in
theorem certificate24610 : ∃ ht : CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31) ∈ j2P,
    AutEFact ↥(CFSG.EvenSporadicStandard.Fin76b.rootGroup ↥j2P ⟨CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31), ht⟩) :=
  KernelC24608.j2_autEFact_t0

end Certificates
