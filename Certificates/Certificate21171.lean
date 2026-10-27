module

public import CFSG.Sporadic.Co2Smith.GlCosetInputs
import Certificates.Kernel.Co2Smith.ChainM2

public section

namespace Certificates

open CertificateChecks

theorem certificate21171 :
    CFSG.Sporadic.Co2Smith.Native.glChainM2OK = true := KernelCo2Smith.chainM2_ok

end Certificates
