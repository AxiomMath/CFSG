module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SigCheck
import CFSG.Certificates.Kernel.EvenSporM22.E32Sound
import Certificates.Kernel.EvenSporM22.E32Checks

public section

open CFSG.EvenSporadicStandard.M22Std.E32Check

namespace CertificateChecks.Batch25911

open CFSG.EvenSporadicStandard.M22Std.E32Check

theorem check_0 : xCheck = true :=
  CFSG.KC.EvenSporM22.xCheck_of KernelEvenSporM22.xPropK_true

end CertificateChecks.Batch25911

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.E32Check in
theorem certificate25911 : xCheck = true := CertificateChecks.Batch25911.check_0

end Certificates
