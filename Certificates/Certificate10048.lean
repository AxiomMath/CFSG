module

public import CFSG.Monster.Tri.LeechLongCheckInputs
import Certificates.Kernel.Tri.Leech10048

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Tri.Leech in
theorem certificate10048 :
    leechLongCheck = true := KernelLeech.leechLong_ok

end Certificates
