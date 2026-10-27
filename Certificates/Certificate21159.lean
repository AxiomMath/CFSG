module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerInputs
import Certificates.Kernel.Co1B.C21159

public section

namespace Certificates

open CertificateChecks

theorem certificate21159 : CFSG.Sporadic.Co1Patterson.Native.innerElemOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.innerGenOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.innerLoopOK = true := KernelCo1B.c21159

end Certificates
