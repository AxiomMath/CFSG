module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Lift8Data

public section

namespace CertificateChecks.Batch36406

open CFSG.OddStandard.AltStdSmall4.G2

set_option maxHeartbeats 0 in
private theorem lift8Check_36406 : lift8Check () = true := by
  decide +kernel

end CertificateChecks.Batch36406

namespace Certificates

open CertificateChecks

theorem certificate36406 : CFSG.OddStandard.AltStdSmall4.G2.lift8Check () = true :=
  CertificateChecks.Batch36406.lift8Check_36406

end Certificates
