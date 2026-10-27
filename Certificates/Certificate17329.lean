module

public import Certificates.Data.TabCo1ThreeC
public meta import Certificates.Data.TabCo1ThreeC
import Certificates.Kernel.Co1B.C17329

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeC in
theorem certificate17329 : threeCCheck () = true := KernelCo1B.Bound17329.c17329

end Certificates
