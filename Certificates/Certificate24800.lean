module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck

public section

open CFSG.EvenSporadicStandard.M22Std.OutCheck

namespace CertificateChecks.Batch24800

open CFSG.EvenSporadicStandard.M22Std.OutCheck

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem s0Check_0 : s0Check = true := by
  decide +kernel

end CertificateChecks.Batch24800

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.OutCheck in
theorem certificate24800 : s0Check = true :=
  CertificateChecks.Batch24800.s0Check_0

end Certificates
