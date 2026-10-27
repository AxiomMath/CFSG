module

public import Certificates.Data.CFSGNative.Co2Smith.Spin8
import CFSG.Certificates.Kernel.Co2SmithS.SpinSound
import Certificates.Kernel.Co2SmithS.SpinK

public section

namespace Certificates

open CertificateChecks

theorem certificate10086 :
    CFSG.Sporadic.Co2Smith.Native.spinCheck = true :=
  CFSG.KC.Co2SmithS.spinCheck_eq.trans KernelCo2SmithS.spinK_ok

end Certificates
