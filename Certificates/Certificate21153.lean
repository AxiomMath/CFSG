module

public import CFSG.Sporadic.Co1Patterson.GraphRonanInputs
import Certificates.Kernel.Co1P.C21153

public section

namespace Certificates

open CertificateChecks

theorem certificate21153 : CFSG.Sporadic.Co1Patterson.Native.ronanCheck2 0 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.ronanCheck2 1 = true := KernelCo1P.c21153

end Certificates
