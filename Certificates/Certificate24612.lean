module

public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
import Certificates.Kernel.Fin76bOm.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.W16 in
theorem certificate24612 : (∃ ht : CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31) ∈ j2P, ∃ elt : ℕ → ↥j2P,
      ELabelling (CFSG.EvenSporadicStandard.Fin76b.rootGroup ↥j2P ⟨CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31), ht⟩)
        (⟨CFSG.Sporadic.SmallOddCore.tp 315 (j2CentTbl 31), ht⟩ : ↥j2P) mulE0 CFSG.EvenSporadicStandard.Fin76b.W16.eT elt) ∧
    UTableSpec mulE0 CFSG.EvenSporadicStandard.Fin76b.W16.eT :=
  ⟨KernelC24608.j2_eLabelling_t0, KernelC24608.j2U_spec⟩

end Certificates
