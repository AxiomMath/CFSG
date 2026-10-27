module

public import CFSG.Monster.GMS.S365CentWitSpecInputs
import Certificates.Kernel.Co1M.C10040

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.S365 in
theorem certificate10040 :
    (witCheckRef = true)
    ∧ (noPatRef = true) := KernelCo1M.c10040

end Certificates
