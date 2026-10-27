module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentSInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
import Certificates.Kernel.ThLet.Glue
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

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271 in
theorem certificate17308 : 
    (∀ r ∈ CFSG.GH74.QTGen4.Recog.G23.g23Words, CFSG.GH74.QTGen4.Recog.G23.evalW
        (fun i : Fin 6 => ThSlp.slpJ a b TabThNative.progE (TabThNative.eIdx i.val)) r = 1) ∧
      (∀ i : Fin 6,
        ThSlp.slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11 *
            ThSlp.slpJ a b TabThNative.progE (TabThNative.eIdx i.val) =
          ThSlp.slpJ a b TabThNative.progE (TabThNative.eIdx i.val) *
            ThSlp.slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11) ∧
      ThSlp.slpJ a b TabThNative.progE (TabThNative.eIdx 0) ≠ 1 :=
  CertificateChecks.KernelThLet.th_letters17308

end Certificates
