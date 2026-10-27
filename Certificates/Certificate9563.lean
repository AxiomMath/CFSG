module

public import Certificates.Data.Item434SporM24
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import all Certificates.Data.Item434SporM24

public section

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

namespace CertificateChecks.Batch9563

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

set_option maxHeartbeats 0 in
private theorem m24_check_0 : m24Check = true := by
  decide +kernel

end CertificateChecks.Batch9563

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem certificate9563 : m24Check = true :=
  CertificateChecks.Batch9563.m24_check_0

end Certificates
