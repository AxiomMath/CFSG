module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCentCheck
import Certificates.Kernel.M22Cent.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.OutCheck in
theorem certificate24803 : centOuterOK = true :=
  @KernelM22Cent.centOuterOK_true

end Certificates
