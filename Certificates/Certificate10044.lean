module

public import CFSG.Monster.GMS.S365RootInputs
import Certificates.Kernel.Co1M.C10044

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module.Pairs in
theorem certificate10044 :
    rootCheck = true := KernelCo1M.c10044

end Certificates
