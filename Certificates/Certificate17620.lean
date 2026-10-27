module

public import Certificates.Data.TabCo1ThreeA
public meta import Certificates.Data.TabCo1ThreeA
import Certificates.Kernel.Co1B.C17620

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA in
theorem certificate17620 : threeACheck () = true := KernelCo1B.Bound17620.c17620

end Certificates
