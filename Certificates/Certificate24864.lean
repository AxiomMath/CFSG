module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24864

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sym6PinData_0 : CFSG.EvenSporadicStandard.M24Std.Sym6.Sym6PinData := by
  decide +kernel

end CertificateChecks.Batch24864

namespace Certificates

open CertificateChecks

theorem certificate24864 : CFSG.EvenSporadicStandard.M24Std.Sym6.Sym6PinData := by
  exact CertificateChecks.Batch24864.sym6PinData_0

end Certificates
