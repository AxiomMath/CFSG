module

public import Certificates.Data.SuzOutComp
import Certificates.Kernel.SuzOut.T2Glue

public section

namespace Certificates

open CFSG.ComponentClassification.SuzOutComp.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.SuzOddCore in
theorem certificate22617 :
    blocksOK 1782 396 t2Lab t2Rep = true ∧
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[0]! = true ∧
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[1]! = true ∧
    t2Gens.size = 2 ∧ t2Gens.size ≤ t2XStrong.size ∧
    (∀ i < t2Gens.size, t2XStrong[i]! = t2Gens[i]!) ∧
    rawChainOK 396 (t2XStrong.extract 0 t2Gens.size) t2XStrong (t2XBase.map Fin.val).toArray
      t2XRaw 4 = true ∧
    rawOrbitSizes 396 t2XStrong (t2XBase.map Fin.val).toArray = [396, 120, 2, 2] ∧
    lettersOK t2Gens.size t2Ab[0]! = true ∧ lettersOK t2Gens.size t2Ab[1]! = true ∧
    isInvA 396 t2A (invCand 396 t2A) = true ∧ isInvA 396 t2B (invCand 396 t2B) = true ∧
    t2O.size ≤ t2DStrong.size ∧ (∀ i < t2O.size, t2DStrong[i]! = t2O[i]!) ∧
    rawChainOK 396 (t2DStrong.extract 0 t2O.size) t2DStrong (t2DBase.map Fin.val).toArray
      t2DRaw 4 = true ∧
    rawOrbitSizes 396 t2DStrong (t2DBase.map Fin.val).toArray = [396, 60, 4] ∧
    CFSG.Quasithin.primCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Hw = true ∧
    reachCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Reach = true ∧
    eqA 396 (CFSG.Quasithin.powA 396 t2A 3) (idA 396) = true ∧ eqA 396 t2A (idA 396) = false ∧
    eqA 396 (CFSG.Quasithin.powA 396 t2B 11) (idA 396) = true ∧ eqA 396 t2B (idA 396) = false ∧
    eqA 396 (CFSG.Quasithin.powA 396 (compA 396 t2A t2B) 11) (idA 396) = true ∧
    eqA 396 (compA 396 t2A t2B) (idA 396) = false ∧
    eqA 396 (compA 396 t2A t2B) (compA 396 t2B t2A) = false :=
  CertificateChecks.KernelSuzOut.T2G.check22617

end Certificates
