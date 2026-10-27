module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Check
import Certificates.Kernel.M22Out24790.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.OutCheck in
theorem certificate24790 : censusCheck = true :=
  KernelM22Out24790.censusCheck_true

end Certificates
