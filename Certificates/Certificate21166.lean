module

public import CFSG.Sporadic.Co2Smith.GlWInputs
import Certificates.Kernel.Co2Smith.W

public section

namespace Certificates

open CertificateChecks

theorem certificate21166 :
    CFSG.Sporadic.Co2Smith.Native.glWOK = true := KernelCo2Smith.w_ok

end Certificates
