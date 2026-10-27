module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.FusionCheck

public section

open CFSG.EvenSporadicStandard.M22Std.FusionCheck

namespace CertificateChecks.Batch24783

open CFSG.EvenSporadicStandard.M22Std.FusionCheck

private theorem fixedCheck_0 : fixedCheck = true := by
  decide +kernel

end CertificateChecks.Batch24783

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.FusionCheck in
theorem certificate24783 : fixedCheck = true :=
  CertificateChecks.Batch24783.fixedCheck_0

end Certificates
