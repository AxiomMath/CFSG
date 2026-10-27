module

public import CFSG.Sporadic.Co2Jc.Native.Forms
import Certificates.Kernel.Co2Jc.Forms

public section

namespace Certificates

open CertificateChecks

theorem certificate719040 :
    CFSG.Sporadic.Co2Jc.Native.formsOK = true := KernelCo2Jc.forms_check

end Certificates
