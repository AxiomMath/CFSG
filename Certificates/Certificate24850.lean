module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairB0

public section

namespace CertificateChecks.Batch24850

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem b0ListData_0 : CFSG.EvenSporadicStandard.M24Std.B0ListData := by
  decide +kernel

end CertificateChecks.Batch24850

namespace Certificates

open CertificateChecks

theorem certificate24850 : CFSG.EvenSporadicStandard.M24Std.B0ListData := CertificateChecks.Batch24850.b0ListData_0

end Certificates
