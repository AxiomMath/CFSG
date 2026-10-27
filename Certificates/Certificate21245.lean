module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
import Certificates.Kernel.Co2Smith.NJ3

public section

namespace Certificates

open CertificateChecks

theorem certificate21245 :
    CFSG.Sporadic.Co2Smith.Native.glNJ3OK = true := KernelCo2Smith.nj3_ok

end Certificates
