module

public import Certificates.Data.U6NA
import Certificates.Kernel.U6NA.Glue

public section

open CFSG.RankThree.PartOne.F106

namespace Certificates

open CFSG.RankThree.PartOne.F106 in
theorem certificate271034 : U6NACheck :=
  CFSG.KD.U6NA.naCheck_true (U6SylowCert.facts_of_check u6ThreeCert
    Certificates.certificate271061)

end Certificates
