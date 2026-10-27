module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Tests
import Certificates.Kernel.LocalComp.J2Std.A4

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15067 : CFSG.ComponentClassification.RankTwoClassical.J2Std.j2A4Check = true := KernelLC.J2Std.j2A4Check_eq_true

end Certificates
