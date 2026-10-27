module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResNonSplit
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch25730

set_option maxHeartbeats 0 in
private theorem nonSplitCheck_0 : CFSG.EvenSporadicStandard.M24Std.Sym6.NonSplitCheck := by
  decide +kernel

end CertificateChecks.Batch25730

namespace Certificates

open CertificateChecks

theorem certificate25730 : CFSG.EvenSporadicStandard.M24Std.Sym6.NonSplitCheck := by
  exact CertificateChecks.Batch25730.nonSplitCheck_0

end Certificates
