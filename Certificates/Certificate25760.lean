module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHLem17Data

public section

namespace CertificateChecks.Batch25760

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem lem17Data_0 : CFSG.EvenSporadicStandard.M24Std.DResH.Lem17Data := by
  decide +kernel

end CertificateChecks.Batch25760

namespace Certificates

open CertificateChecks

theorem certificate25760 : CFSG.EvenSporadicStandard.M24Std.DResH.Lem17Data :=
  CertificateChecks.Batch25760.lem17Data_0

end Certificates
