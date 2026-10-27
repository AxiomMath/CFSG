module

public import Certificates.Data.Y2L.ClaimA

public section

namespace CertificateChecks.Batch442314

open CFSG.OddStandard.HigherRank.G2Three.Sec2

set_option maxHeartbeats 0 in
private theorem claimA_check : y2l_claimACheck () = true := by
  decide +kernel

end CertificateChecks.Batch442314

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.HigherRank.G2Three.Sec2 in
theorem certificate442314 : y2l_claimACheck () = true :=
  CertificateChecks.Batch442314.claimA_check

end Certificates
