module

public import Certificates.Data.TabCo1Reps
import Certificates.Kernel.Co1B.C17328
public import CFSG.Sporadic.Co1Block.XFixBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1 in
theorem certificate17328 : xFixCount certVecs repD1 = 60 := KernelCo1B.C17328.c17328

end Certificates
