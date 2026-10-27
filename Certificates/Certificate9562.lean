module

public import Certificates.Data.Item434SporM23
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import all Certificates.Data.Item434SporM23

public section

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

namespace CertificateChecks.Batch9562

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

set_option maxHeartbeats 0 in
private theorem m23_check_0 : m23Check = true := by
  decide +kernel

end CertificateChecks.Batch9562

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem certificate9562 : m23Check = true :=
  CertificateChecks.Batch9562.m23_check_0

end Certificates
