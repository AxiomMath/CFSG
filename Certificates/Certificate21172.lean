module

public import CFSG.Sporadic.Co2Smith.GlCosetInputs
import Certificates.Kernel.Co2Smith.ChainCz

public section

namespace Certificates

open CertificateChecks

theorem certificate21172 :
    CFSG.Sporadic.Co2Smith.Native.glChainCzOK = true := KernelCo2Smith.chainCz_ok

end Certificates
