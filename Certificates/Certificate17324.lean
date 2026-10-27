module

public import Certificates.Data.TabCo1FiveA
public meta import Certificates.Data.TabCo1FiveA
import Certificates.Kernel.Co1B.C17324

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA in
theorem certificate17324 : fiveACheck () = true := KernelCo1B.Bound17324.c17324

end Certificates
