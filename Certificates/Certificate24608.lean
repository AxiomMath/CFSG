
module

public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
import Certificates.Kernel.Fin76bOm.Bridge
import CFSG.Sporadic.Schreier.PairJ2CertInputs
import CFSG.Sporadic.Schreier.PairJ2CheckInputs
import CFSG.Sporadic.SmallOddCore.J2CheckInputs
meta import CFSG.Sporadic.SmallOddCore.J2Data
meta import CFSG.Sporadic.Schreier.PairJ2Check
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69Def
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.NotZ2A6Base
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest9

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b in
theorem certificate24608 : ∃ ht : CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31) ∈ j2P, RootFactsFor ↥j2P ⟨CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31), ht⟩ :=
  KernelC24608.j2_rootFactsFor_t0

end Certificates
