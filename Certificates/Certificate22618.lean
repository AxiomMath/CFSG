module

public import Certificates.Data.SuzOutComp
import Certificates.Kernel.SuzOut.T3Glue

public section

namespace Certificates

open CFSG.ComponentClassification.SuzOutComp.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.SuzOddCore in
theorem certificate22618 :
    (CFSG.Sporadic.SuzOddCore.fixList 3).length = 100 ∧ (kGens 3).size = 5 ∧ (kGens 3).size ≤ t3XStrong.size ∧
    (∀ i < (kGens 3).size, t3XStrong[i]! = (kGens 3)[i]!) ∧
    rawChainOK 100 (t3XStrong.extract 0 (kGens 3).size) t3XStrong (t3XBase.map Fin.val).toArray
      t3XRaw 4 = true ∧
    rawOrbitSizes 100 t3XStrong (t3XBase.map Fin.val).toArray = [100, 63, 24, 8] ∧
    lettersOK (kGens 3).size t3Ab[0]! = true ∧ lettersOK (kGens 3).size t3Ab[1]! = true ∧
    isInvA 100 t3A (invCand 100 t3A) = true ∧ isInvA 100 CFSG.ComponentClassification.SuzOutComp.Native.t3B (invCand 100 CFSG.ComponentClassification.SuzOutComp.Native.t3B) = true ∧
    t3O.size ≤ t3DStrong.size ∧ (∀ i < t3O.size, t3DStrong[i]! = t3O[i]!) ∧
    rawChainOK 100 (t3DStrong.extract 0 t3O.size) t3DStrong (t3DBase.map Fin.val).toArray
      t3DRaw 4 = true ∧
    rawOrbitSizes 100 t3DStrong (t3DBase.map Fin.val).toArray = [100, 63, 24, 4] ∧
    CFSG.Quasithin.primCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Hw = true ∧
    reachCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Reach = true ∧
    eqA 100 (CFSG.Quasithin.powA 100 t3A 3) (idA 100) = true ∧ eqA 100 t3A (idA 100) = false ∧
    eqA 100 (CFSG.Quasithin.powA 100 CFSG.ComponentClassification.SuzOutComp.Native.t3B 7) (idA 100) = true ∧ eqA 100 CFSG.ComponentClassification.SuzOutComp.Native.t3B (idA 100) = false ∧
    eqA 100 (CFSG.Quasithin.powA 100 (compA 100 t3A CFSG.ComponentClassification.SuzOutComp.Native.t3B) 5) (idA 100) = true ∧
    eqA 100 (compA 100 t3A CFSG.ComponentClassification.SuzOutComp.Native.t3B) (idA 100) = false ∧
    eqA 100 (compA 100 t3A CFSG.ComponentClassification.SuzOutComp.Native.t3B) (compA 100 CFSG.ComponentClassification.SuzOutComp.Native.t3B t3A) = false :=
  CertificateChecks.KernelSuzOut.T3G.check22618

end Certificates
