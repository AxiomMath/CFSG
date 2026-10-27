module

public import CFSG.LargeExtraspecial.S63DSchurInputs

public section

open CFSG.LargeExtraspecial.S63

namespace CertificateChecks.Batch21180

open CFSG.LargeExtraspecial.S63

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem d4SplitCheck_eq : d4SplitCheck = true := by
  decide +kernel

end CertificateChecks.Batch21180

namespace Certificates

open CertificateChecks

open CFSG.LargeExtraspecial.S63 in
theorem certificate21180 : d4SplitCheck = true :=
  CertificateChecks.Batch21180.d4SplitCheck_eq

end Certificates
