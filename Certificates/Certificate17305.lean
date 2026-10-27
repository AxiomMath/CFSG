module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
import Certificates.Kernel.ThCensus.Glue
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace Certificates

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate17305 :     orderOf (ThSlp.slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) = 3 ∧
      orderOf ThCent.zJ = 3 ∧
      orderOf (ThSlp.slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) = 3 ∧
      ∀ x : ↥J, orderOf x = 3 → ∃ k c : ↥J,
        (c = ThSlp.slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11 ∨
          c = ThCent.zJ ∨
          c = ThSlp.slpJ a b CFSG.HardMathSupport.Dickson.I271.TabThNative.progU 22) ∧
        ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = x :=
  CertificateChecks.KernelThCensus.th_census17305

end Certificates
