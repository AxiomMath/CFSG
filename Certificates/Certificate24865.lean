module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24865

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sigEnum_0 : CFSG.EvenSporadicStandard.M24Std.Sym6.SigEnum := by
  decide +kernel

end CertificateChecks.Batch24865

namespace Certificates

open CertificateChecks

theorem certificate24865 : CFSG.EvenSporadicStandard.M24Std.Sym6.SigEnum := by
  exact CertificateChecks.Batch24865.sigEnum_0

end Certificates
