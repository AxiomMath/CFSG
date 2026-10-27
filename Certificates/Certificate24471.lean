module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FixedCheck

public section

open CFSG.EvenSporadicStandard.M23Std.FusionCheck

namespace CertificateChecks.Batch24471

open CFSG.EvenSporadicStandard.M23Std.FusionCheck

theorem fixedCheck_0 : fixedCheck = true := by
  decide +kernel

end CertificateChecks.Batch24471

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M23Std.FusionCheck in
theorem certificate24471 : fixedCheck = true := CertificateChecks.Batch24471.fixedCheck_0

end Certificates
