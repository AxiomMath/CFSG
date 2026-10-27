module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Data

public section

open CFSG.RankThree.PartTwo.Sec4.Item434F42

namespace CertificateChecks.Batch9615

open CFSG.RankThree.PartTwo.Sec4.Item434F42

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem f42_check : f42Check f42Data = true := by
  decide +kernel

end CertificateChecks.Batch9615

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434F42 in
theorem certificate9615 : f42Check f42Data = true := by
  exact CertificateChecks.Batch9615.f42_check

end Certificates
