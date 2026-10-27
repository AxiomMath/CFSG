module

public import CFSG.Sporadic.Co2Smith.GlU62WeylInputs
import Certificates.Kernel.Co2Smith.Weyl

public section

namespace Certificates

open CertificateChecks

theorem certificate21186 :
    CFSG.Sporadic.Co2Smith.Native.glWeylChartOK = true := KernelCo2Smith.weylChart_ok

end Certificates
