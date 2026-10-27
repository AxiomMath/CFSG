module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
import Certificates.Kernel.LocalComp.Co3IdentModel

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate3093 : treeTabOK 276 gArrs hPar hLab hList 4608 = true ∧ keysOK [0, 1] hList 4608 = true ∧
      (∀ i < 7, isInvA 276 mGenArrs[i]! (invCand 276 mGenArrs[i]!) = true) ∧
      conjTabOK 276 mGenArrs (mGenArrs.map (invCand 276)) cBFS.2.1 cBFS.2.2 cBFS.1 (genArr 0)
        630 = true ∧
      keysOK [0, 1, 2, 3] cBFS.1 630 = true ∧
      (∀ k < 6, commutesA 276 (posArr (edgeFirst k)) (genArr 0) = true) := KernelLC.Co3Id.facts3093

end Certificates
