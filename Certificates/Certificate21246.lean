module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
import Certificates.Kernel.Co2Smith.ChainJc

public section

namespace Certificates

open CertificateChecks

theorem certificate21246 :
    CFSG.Sporadic.Co2Smith.Native.glNJChainOK = true := KernelCo2Smith.chainJc_ok

end Certificates
