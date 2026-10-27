module

public import CFSG.Monster.GMS.S365CenterOrbInputs
import Certificates.Kernel.Co1M.C10041

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.S365 in
theorem certificate10041 :
    orbitCheck3 = true := KernelCo1M.c10041

end Certificates
