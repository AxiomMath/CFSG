module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataDefs
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24846

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem qdFixData_0 : CFSG.EvenSporadicStandard.M24Std.QdFixData := by
  decide +kernel

end CertificateChecks.Batch24846

namespace Certificates

open CertificateChecks

theorem certificate24846 : CFSG.EvenSporadicStandard.M24Std.QdFixData := by
  exact CertificateChecks.Batch24846.qdFixData_0

end Certificates
