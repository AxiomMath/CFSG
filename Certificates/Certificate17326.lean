module

public import Certificates.Data.TabCo1FiveC
public meta import Certificates.Data.TabCo1FiveC
import Certificates.Kernel.Co1B.C17326

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveC in
theorem certificate17326 : fiveCCheck () = true := KernelCo1B.Bound17326.c17326

end Certificates
