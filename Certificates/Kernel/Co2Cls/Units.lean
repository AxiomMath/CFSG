module

public import Certificates.Kernel.Co2Cls.Bind
public import CFSG.Certificates.Kernel.Co2Cls.Units

public section

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2Cls

theorem isUnit_C : ∀ x ∈ genMonN 21 GC, IsUnit x := genMonN_isUnit inv

end CertificateChecks.KernelSpor.Co2Cls

end
