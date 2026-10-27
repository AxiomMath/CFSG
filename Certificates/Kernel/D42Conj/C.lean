module

public import Certificates.Data.Kernel.D42ConjP
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeD42ConjData
public import Certificates.Kernel.D4Plane.Checks
public import Certificates.Kernel.D42Conj.D

public section

namespace CFSG.KD.D42Conj

open CFSG.KC.D4PlaneP CFSG.KC.D42ConjP CFSG.KD.D4Plane
open CFSG.LocalAnalysis.AGL81I.Section3.D42Over

theorem ixOK : ixAllP ls (wordP ls kAW) (wordP ls kBW) d42ConjWords es ix = true := by
  decide +kernel

end CFSG.KD.D42Conj

end
