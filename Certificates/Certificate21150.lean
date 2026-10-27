module

public import CFSG.Sporadic.Co1Patterson.GraphInputs
import Certificates.Kernel.Co1P.C21150

public section

namespace Certificates

open CertificateChecks

theorem certificate21150 : CFSG.Sporadic.Co1Patterson.Native.suborbCheck1 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.suborbCheck2 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.suborbCheck3 = true := KernelCo1P.c21150

end Certificates
