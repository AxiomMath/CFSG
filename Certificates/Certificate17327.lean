module

public import Certificates.Data.TabCo1Census
public meta import Certificates.Data.TabCo1Census
import Certificates.Kernel.Co1ThreeK.GlueCensus

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1Census in
theorem certificate17327 : censusCheck () = true := KernelCo1ThreeK.c17327

end Certificates
