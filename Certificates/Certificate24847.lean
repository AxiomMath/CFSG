module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataDefs
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24847

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem qdGen45Data_0 : CFSG.EvenSporadicStandard.M24Std.QdGen45Data := by
  decide +kernel

end CertificateChecks.Batch24847

namespace Certificates

open CertificateChecks

theorem certificate24847 : CFSG.EvenSporadicStandard.M24Std.QdGen45Data := by
  exact CertificateChecks.Batch24847.qdGen45Data_0

end Certificates
