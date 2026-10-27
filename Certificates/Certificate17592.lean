module

public import Certificates.Data.TabCo1ThreeDRoot
public meta import Certificates.Data.TabCo1ThreeDRoot
import Certificates.Kernel.Co1B.C17592

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot in
theorem certificate17592 : CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot.rootCheck () = true := KernelCo1B.Bound17592.c17592

end Certificates
