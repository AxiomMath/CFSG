module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Check
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24860

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem alt8PinData_0 : CFSG.EvenSporadicStandard.M24Std.Alt8.Alt8PinData := by
  decide +kernel

end CertificateChecks.Batch24860

namespace Certificates

open CertificateChecks

theorem certificate24860 : CFSG.EvenSporadicStandard.M24Std.Alt8.Alt8PinData := by
  exact CertificateChecks.Batch24860.alt8PinData_0

end Certificates
