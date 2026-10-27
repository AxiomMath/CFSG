module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import Certificates.Certificate1022
import Certificates.Kernel.ThCent.Consumers
import Certificates.Certificate1021
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

theorem certificate17252 : 
    Nat.card (Subgroup.centralizer
      ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
        CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11)} :
          Set CFSG.Sporadic.Th.J)) ≤ 15921360 :=
  KernelThCent.card_centralizer_s3_le th_kernel_facts_ok

end Certificates
