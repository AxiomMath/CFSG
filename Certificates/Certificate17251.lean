module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import Certificates.Certificate1022
import Certificates.Kernel.Th3Local.Glue
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative in
theorem certificate17251 : 
    orderOf (slpJ a b prog3 11) = 3 ∧ orderOf (slpJ a b prog3 14) = 7 ∧
      orderOf (slpJ a b prog3 12) = 13 ∧
      slpJ a b prog3 11 * slpJ a b prog3 14 = slpJ a b prog3 14 * slpJ a b prog3 11 ∧
      slpJ a b prog3 11 * slpJ a b prog3 12 = slpJ a b prog3 12 * slpJ a b prog3 11 :=
  KernelTh3Local.th3_local

end Certificates
