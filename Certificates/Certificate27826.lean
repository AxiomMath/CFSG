module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCheck
import Certificates.Kernel.U43Rho.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate27826 : CFSG.EvenSporadicStandard.Fin76b.U16.d8Check = true ∧
    CFSG.EvenSporadicStandard.Fin76b.U16.rhoCosetCheck = true := KernelU43Rho.facts27826

end Certificates
