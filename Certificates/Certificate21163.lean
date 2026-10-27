module

public import CFSG.Sporadic.Co2Smith.GlC0QuotInputs
import Certificates.Kernel.Co2Smith.Qt

public section

namespace Certificates

open CertificateChecks

theorem certificate21163 :
    CFSG.Sporadic.Co2Smith.Native.glQtOK = true := KernelCo2Smith.qt_ok

end Certificates
