module

public import CFSG.Sporadic.Co1Patterson.GraphInputs
import Certificates.Kernel.Co1P.C21151

public section

namespace Certificates

open CertificateChecks

theorem certificate21151 : CFSG.Sporadic.Co1Patterson.Native.suborbCheck4 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.suborbCheck5 = true := KernelCo1P.c21151

end Certificates
