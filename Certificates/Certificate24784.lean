module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.A6Cent

public section

open CFSG.EvenSporadicStandard.M22Std

namespace CertificateChecks.Batch24784

open CFSG.EvenSporadicStandard.M22Std

theorem a6CentCheck_0 : a6CentCheck = true := by
  decide +kernel

end CertificateChecks.Batch24784

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std in
theorem certificate24784 : a6CentCheck = true := CertificateChecks.Batch24784.a6CentCheck_0

end Certificates
