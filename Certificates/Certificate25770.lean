module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6Data

public section

namespace CertificateChecks.Batch25770

private theorem a6InvData_0 : CFSG.EvenSporadicStandard.M24Std.DRes.A6InvData := by
  decide +kernel

end CertificateChecks.Batch25770

namespace Certificates

open CertificateChecks

theorem certificate25770 : CFSG.EvenSporadicStandard.M24Std.DRes.A6InvData :=
  CertificateChecks.Batch25770.a6InvData_0

end Certificates
