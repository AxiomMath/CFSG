module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
import Certificates.Kernel.Fin76bOm.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.W16 in
theorem certificate24613 : (∃ ht : CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9) ∈ j3P, ∃ elt : ℕ → ↥j3P,
      ELabelling (CFSG.EvenSporadicStandard.Fin76b.rootGroup ↥j3P ⟨CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9), ht⟩)
        (⟨CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9), ht⟩ : ↥j3P) mulEJ3 CFSG.EvenSporadicStandard.Fin76b.W16.eT elt) ∧
    UTableSpec mulEJ3 CFSG.EvenSporadicStandard.Fin76b.W16.eT :=
  ⟨KernelC24608.j3_eLabelling_t0, KernelC24608.j3U_spec⟩

end Certificates
