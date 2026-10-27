module

public import CFSG.Sporadic.Co2Smith.GlU62D1Inputs
import Certificates.Kernel.Co2Smith.D1

public section

namespace Certificates

open CertificateChecks

theorem certificate21187 :
    CFSG.Sporadic.Co2Smith.Native.d1OK = true := KernelCo2Smith.d1_ok

end Certificates
