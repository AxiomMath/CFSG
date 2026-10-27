module

public import CFSG.RankThree.PartTwo.Sec12.KS128BCensusM12Inputs

public section

open CFSG.RankThree.PartTwo.Sec12.BCensus

namespace CertificateChecks.Batch8115

open CFSG.RankThree.PartTwo.Sec12.BCensus

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem cz_check_0 : czCheck = true := by
  decide +kernel

end CertificateChecks.Batch8115

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec12.BCensus in
theorem certificate8115 : czCheck = true := by
  exact CertificateChecks.Batch8115.cz_check_0

end Certificates
