module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FusionCheck

public section

open CFSG.EvenSporadicStandard.M23Std.FusionCheck

namespace CertificateChecks.Batch24470

open CFSG.EvenSporadicStandard.M23Std.FusionCheck

theorem fusionCheck_0 : fusionCheck = true := by
  decide +kernel

end CertificateChecks.Batch24470

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M23Std.FusionCheck in
theorem certificate24470 : fusionCheck = true := CertificateChecks.Batch24470.fusionCheck_0

end Certificates
