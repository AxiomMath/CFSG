module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentUInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import Certificates.Certificate1022
import Certificates.Kernel.ThCent.Leaf3C
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

theorem certificate17306 : 
    Nat.card (Subgroup.centralizer
      ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
        CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)} :
          Set CFSG.Sporadic.Th.J)) ≤ 174960 :=
  KernelThCent.card_centralizer_u_le th_kernel_facts_ok

end Certificates
