module

public import CFSG.Monster.Tri.LeechCheckInputs
import Certificates.Kernel.Tri.Leech10047

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Tri.Leech in
theorem certificate10047 :
    leechCheck = true := KernelLeech.leech_ok

end Certificates
