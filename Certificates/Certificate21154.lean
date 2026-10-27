module

public import CFSG.Sporadic.Co1Patterson.GraphRonanInputs
import Certificates.Kernel.Co1P.C21154

public section

namespace Certificates

open CertificateChecks

theorem certificate21154 : CFSG.Sporadic.Co1Patterson.Native.q2Check 0 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 1 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 2 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 3 = true := KernelCo1P.c21154

end Certificates
