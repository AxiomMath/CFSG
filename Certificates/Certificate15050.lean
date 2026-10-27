module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Tests
import Certificates.Kernel.LocalComp.J2Std.Std

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15050 : CFSG.ComponentClassification.RankTwoClassical.J2Std.j2StdCheck = true := KernelLC.J2Std.j2StdCheck_eq_true

end Certificates
