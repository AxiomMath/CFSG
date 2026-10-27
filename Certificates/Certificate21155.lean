module

public import CFSG.Sporadic.Co1Patterson.GraphRonanInputs
import Certificates.Kernel.Co1P.C21155

public section

namespace Certificates

open CertificateChecks

theorem certificate21155 : CFSG.Sporadic.Co1Patterson.Native.q2Check 4 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 5 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 6 = true := KernelCo1P.c21155

end Certificates
