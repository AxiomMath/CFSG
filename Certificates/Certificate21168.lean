module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
import Certificates.Kernel.Co2Smith.NJ1

public section

namespace Certificates

open CertificateChecks

theorem certificate21168 :
    CFSG.Sporadic.Co2Smith.Native.glNJ1OK = true := KernelCo2Smith.nj1_ok

end Certificates
