module

public import Certificates.Data.F4ThreeRank
import Certificates.Kernel.F4Three.Checks
import CFSG.Certificates.Kernel.F4ThreeSound

public section

open CFSG.RankThree.PartOne.F106

namespace Certificates

open CFSG.RankThree.PartOne.F106 in
theorem certificate271060 : F4ThreeRankCheck := by
  exact CFSG.KC.F4Three.check_of f4ThreeCert CFSG.KC.F4Three.D.GB CFSG.KC.F4Three.D.TT
    CFSG.KC.F4Three.ch271060_small CFSG.KC.F4Three.ch271060_lens CFSG.KC.F4Three.ch271060_gb
    CFSG.KC.F4Three.ch271060_tab CFSG.KC.F4Three.ch271060_nod CFSG.KC.F4Three.ch271060_rt
    CFSG.KC.F4Three.ch271060_inv CFSG.KC.F4Three.ch271060_wit

end Certificates
