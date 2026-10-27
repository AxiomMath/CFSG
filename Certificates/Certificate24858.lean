module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLetters
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24858

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem letterData_0 : CFSG.EvenSporadicStandard.M24Std.SplitB.LetterData := by
  decide +kernel

end CertificateChecks.Batch24858

namespace Certificates

open CertificateChecks

theorem certificate24858 : CFSG.EvenSporadicStandard.M24Std.SplitB.LetterData := by
  exact CertificateChecks.Batch24858.letterData_0

end Certificates
