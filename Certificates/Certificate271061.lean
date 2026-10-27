module

public import Certificates.Data.U6ThreeRank
import Certificates.Kernel.U6Three.Checks
import CFSG.Certificates.Kernel.U6ThreeSound

public section

open CFSG.RankThree.PartOne.F106 CFSG.KC.U6Three

namespace Certificates

open CFSG.RankThree.PartOne.F106 in
theorem certificate271061 : U6ThreeRankCheck :=
  check_of D.TP D.IP D.JP ch271061_paths ch271061_path0 ch271061_letters ch271061_zl
    ch271061_lens ch271061_tab ch271061_inj ch271061_inv ch271061_rt ch271061_wit

end Certificates
