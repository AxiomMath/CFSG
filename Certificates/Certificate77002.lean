module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosG2Check
import Certificates.Kernel.G2Three.Q16Checks
import Certificates.Kernel.G2Three.Final
import CFSG.Certificates.Kernel.G2Three.Q16Sound

public section

namespace Certificates

open CFSG.CGT.PushingUpLit.SolKNA CFSG.RankThree.PartTwo.Census.Carrier.G2Three in
theorem certificate77002 : q16Free elemsS = true :=
  CFSG.KC.G2Three.q16Free_of_K CFSG.KD.G2Three.consts_ok CFSG.KD.G2Three.bone (by decide)
    CFSG.KD.G2Three.tabS.1 CFSG.KD.G2Three.tabS.2.2.2.2 CFSG.KD.G2Three.ch77002_k

end Certificates
