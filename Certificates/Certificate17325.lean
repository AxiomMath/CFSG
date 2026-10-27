module

public import Certificates.Data.TabCo1FiveB
public meta import Certificates.Data.TabCo1FiveB
import Certificates.Kernel.Co1B.C17325

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB in
theorem certificate17325 : fiveBCheck () = true := KernelCo1B.Bound17325.c17325

end Certificates
