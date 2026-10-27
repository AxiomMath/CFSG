module

public import CFSG.Sporadic.Co2Smith.GlDataRootInputs
import Certificates.Kernel.Co2Smith.Root

public section

namespace Certificates

open CertificateChecks

theorem certificate21126 :
    CFSG.Sporadic.Co2Smith.Native.glRootOK = true := KernelCo2Smith.root_ok

end Certificates
