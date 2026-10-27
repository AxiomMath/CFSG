
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UData
import Certificates.Kernel.U43Rho.Glue26080

public section

namespace Certificates

open CertificateChecks

theorem certificate26080 : CFSG.EvenSporadicStandard.Fin76b.rhoOK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.countBadP = 0 ∧
    CFSG.EvenSporadicStandard.Fin76b.countBadRho = 0 := KernelU43Rho.facts26080

end Certificates
