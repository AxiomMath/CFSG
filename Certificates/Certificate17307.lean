module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import Certificates.Certificate1022
import Certificates.Kernel.ThCentU.Glue
import Certificates.Certificate17306
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

theorem certificate17307 : 
    Nat.card (Subgroup.centralizer
      ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
        CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)} :
          Set CFSG.Sporadic.Th.J)) = 174960 ∧
    Subgroup.centralizer
      ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
        CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)} :
          Set CFSG.Sporadic.Th.J) =
      Subgroup.closure
        {CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
          CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 20,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
          CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 21} ∧
    ∃ R : Subgroup CFSG.Sporadic.Th.J,
      R ≤ Subgroup.centralizer
        ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
          CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)} :
            Set CFSG.Sporadic.Th.J) ∧
      (∀ x ∈ Subgroup.centralizer
        ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
          CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)} :
            Set CFSG.Sporadic.Th.J), ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      Nat.card R = 3 ^ 5 ∧
      ∀ x ∈ Subgroup.centralizer
        ({(CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp.slpJ CFSG.Sporadic.Th.a
          CFSG.Sporadic.Th.b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22)} :
            Set CFSG.Sporadic.Th.J), (∀ r ∈ R, x * r = r * x) → x ∈ R :=
  KernelThCentU.th_centU17307

end Certificates
