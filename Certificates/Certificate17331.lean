module

public import Certificates.Data.TabCo1ThreeMoore
public meta import Certificates.Data.TabCo1ThreeMoore
import Certificates.Kernel.Co1ThreeK.GlueMoore

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore in
theorem certificate17331 : mooreCheck () = true := KernelCo1ThreeK.c17331

end Certificates
