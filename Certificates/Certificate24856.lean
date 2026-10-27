module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBBasis
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24856

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem basisData_0 : CFSG.EvenSporadicStandard.M24Std.SplitB.BasisData := by
  decide +kernel

end CertificateChecks.Batch24856

namespace Certificates

open CertificateChecks

theorem certificate24856 : CFSG.EvenSporadicStandard.M24Std.SplitB.BasisData := by
  exact CertificateChecks.Batch24856.basisData_0

end Certificates
