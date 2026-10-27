module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerInputs
import Certificates.Kernel.Co1P.C21235

public section

namespace Certificates

open CertificateChecks

theorem certificate21235 : CFSG.Sporadic.Co1Patterson.Native.innerBfsOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.innerOrbOK = true := KernelCo1P.c21235

end Certificates
