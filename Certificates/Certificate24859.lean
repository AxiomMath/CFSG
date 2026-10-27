module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLetters
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24859

theorem dualData_0 : CFSG.EvenSporadicStandard.M24Std.SplitB.DualData := by
  decide +kernel

end CertificateChecks.Batch24859

namespace Certificates

open CertificateChecks

theorem certificate24859 : CFSG.EvenSporadicStandard.M24Std.SplitB.DualData := CertificateChecks.Batch24859.dualData_0

end Certificates
