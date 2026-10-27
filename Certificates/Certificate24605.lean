module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
import Certificates.Kernel.Sporadic.OddCore.J3BetaA5F

public section

namespace Certificates

open CertificateChecks

theorem certificate24605 : CFSG.EvenSporadicStandard.Fin76b.Beta.j3A5OK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.Beta.j3A5MemOK = true :=
  ⟨KernelSpor.J3BetaA5.facts24605a, KernelSpor.J3BetaA5.facts24605b⟩

end Certificates
