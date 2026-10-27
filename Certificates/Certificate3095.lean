module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCubeInputs
import Certificates.Kernel.LocalComp.Co3IdentCubeK

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Co3.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Monster.B.Co2.Native in
theorem certificate3095 : ∀ j < 4608, commutesA 276 hList[j]! yArr = true →
      ((allLt 4608 fun i => !commutesA 276 hList[i]! yArr ||
        eqA 276 (compA 276 kpArr (compA 276 hList[i]! (compA 276 kpArr hList[j]!)))
          (compA 276 hList[j]! hList[i]!)) &&
        eqA 276 (compA 276 uArr hList[j]!) (compA 276 hList[j]! uArr)) =
      (eqA 276 hList[j]! kpArr || eqA 276 hList[j]! kpcArr) := KernelLC.Co3Id.facts3095

end Certificates
