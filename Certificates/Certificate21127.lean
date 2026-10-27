module

public import CFSG.Sporadic.Co2Smith.GlDataRootInputs
import Certificates.Kernel.Co2Smith.ChainG0

public section

namespace Certificates

open CertificateChecks

theorem certificate21127 :
    CFSG.Sporadic.Co2Smith.Native.glChainG0OK = true := KernelCo2Smith.chainG0_ok

end Certificates
