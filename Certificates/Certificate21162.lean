module

public import CFSG.Sporadic.Co2Smith.GlC0FixInputs
import Certificates.Kernel.Co2Smith.Fix

public section

namespace Certificates

open CertificateChecks

theorem certificate21162 :
    CFSG.Sporadic.Co2Smith.Native.glMkFixOK = true := KernelCo2Smith.fix_ok

end Certificates
