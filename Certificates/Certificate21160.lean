module

public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import Certificates.Kernel.Co2Smith.Mark

public section

namespace Certificates

open CertificateChecks

theorem certificate21160 :
    CFSG.Sporadic.Co2Smith.Native.glMarkOK = true := KernelCo2Smith.mark_ok

end Certificates
