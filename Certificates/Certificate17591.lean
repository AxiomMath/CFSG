module

public import Certificates.Data.TabCo1ThreeD
public meta import Certificates.Data.TabCo1ThreeD
import Certificates.Kernel.Co1B.C17591

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD in
theorem certificate17591 : threeDCheck () = true := KernelCo1B.Bound17591.c17591

end Certificates
