module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.FusionCheck

public section

open CFSG.EvenSporadicStandard.M22Std.FusionCheck

namespace CertificateChecks.Batch24782

open CFSG.EvenSporadicStandard.M22Std.FusionCheck

private theorem fusionCheck_0 : fusionCheck = true := by
  decide +kernel

end CertificateChecks.Batch24782

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.FusionCheck in
theorem certificate24782 : fusionCheck = true :=
  CertificateChecks.Batch24782.fusionCheck_0

end Certificates
