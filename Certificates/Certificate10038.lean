module

public import CFSG.Monster.GMS.S365CentRootSpecInputs
import Certificates.Kernel.Co1M.C10038

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.S365 in
theorem certificate10038 :
    (rootCount120 = true)
    ∧ (rootFixOK = true) := KernelCo1M.c10038

end Certificates
