module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Check
import CFSG.Certificates.Kernel.EvenSporM22.E32Sound
import Certificates.Kernel.EvenSporM22.E32Checks

public section

open CFSG.EvenSporadicStandard.M22Std.E32Check

namespace CertificateChecks.Batch25930

open CFSG.EvenSporadicStandard.M22Std.E32Check

theorem check_0 : check = true :=
  CFSG.KC.EvenSporM22.check_of KernelEvenSporM22.checkPropK_true

end CertificateChecks.Batch25930

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.E32Check in
theorem certificate25930 : check = true := CertificateChecks.Batch25930.check_0

end Certificates
