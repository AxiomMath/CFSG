module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLiftData
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24857

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem liftBData_0 : CFSG.EvenSporadicStandard.M24Std.SplitB.LiftBData := by
  decide +kernel

end CertificateChecks.Batch24857

namespace Certificates

open CertificateChecks

theorem certificate24857 : CFSG.EvenSporadicStandard.M24Std.SplitB.LiftBData := by
  exact CertificateChecks.Batch24857.liftBData_0

end Certificates
