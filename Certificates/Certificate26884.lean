module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck

public section

open CFSG.EvenSporadicStandard.M22Std.HS08Check

namespace CertificateChecks.Batch26884

open CFSG.EvenSporadicStandard.M22Std.HS08Check

private theorem genInvCheck_0 : genInvCheck = true := by
  decide +kernel

end CertificateChecks.Batch26884

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.HS08Check in
theorem certificate26884 : genInvCheck = true :=
  CertificateChecks.Batch26884.genInvCheck_0

end Certificates
