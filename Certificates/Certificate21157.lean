module

public import CFSG.Sporadic.Co1Patterson.AmalgamInputs
import Certificates.Kernel.Co1P.C21157

public section

namespace Certificates

open CertificateChecks

theorem certificate21157 : CFSG.Sporadic.Co1Patterson.Native.amalgamCheck = true := KernelCo1P.c21157

end Certificates
