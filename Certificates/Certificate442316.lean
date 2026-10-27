module

public import Certificates.Kernel.G2Three.Final
public import Certificates.Kernel.G2Three.Y2LNGChecks
public import CFSG.Certificates.Kernel.G2Three.Y2LNGSound

public section

namespace Certificates

open CFSG.OddStandard.HigherRank.G2Three.Sec2 in
theorem certificate442316 : y2l_ngCheck () = true :=
  by
    rw [CFSG.KC.G2Three.ngCheck_eq CFSG.KD.G2Three.consts_ok CFSG.KD.G2Three.gA_ok
      CFSG.KD.G2Three.bone]
    exact CFSG.KD.G2Three.ngK_ok

end Certificates
