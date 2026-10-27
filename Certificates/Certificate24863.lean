module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBCentCheck

public section

namespace CertificateChecks.Batch24863

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem splitBCentData_0 : CFSG.EvenSporadicStandard.M24Std.SplitBCentData := by
  decide +kernel

end CertificateChecks.Batch24863

namespace Certificates

open CertificateChecks

theorem certificate24863 : CFSG.EvenSporadicStandard.M24Std.SplitBCentData := by
  exact CertificateChecks.Batch24863.splitBCentData_0

end Certificates
