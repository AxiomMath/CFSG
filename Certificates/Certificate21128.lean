module

public import CFSG.Sporadic.Co2Smith.GlDataF0Inputs
import Certificates.Kernel.Co2Smith.F0

public section

namespace Certificates

open CertificateChecks

theorem certificate21128 :
    CFSG.Sporadic.Co2Smith.Native.glF0OK = true := KernelCo2Smith.f0_ok

end Certificates
