
module


public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsInputs
import Certificates.Kernel.LocalComp.Co3IdentFactsK

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate3094 : relsV.all (fun r => eqA 276 (wordArr r) (idA 276)) = true ∧
      commutesA 276 (genArr 3) (genArr 2) = true ∧ commutesA 276 (genArr 3) (genArr 5) = true ∧
      eqA 276 (genArr 0) (genArr 4) = false ∧ eqA 276 (genArr 0) (idA 276) = false ∧
      eqA 276 (compA 276 (genArr 0) (genArr 0)) (idA 276) = true ∧
      (∀ j < 4608, (commutesA 276 hList[j]! gArrs[0]! && commutesA 276 hList[j]! gArrs[1]! &&
        commutesA 276 hList[j]! gArrs[2]!) = true →
        (eqA 276 hList[j]! (idA 276) || eqA 276 hList[j]! (genArr 4) ||
          eqA 276 hList[j]! (genArr 0) || eqA 276 hList[j]! eaArr) = true) ∧
      ((List.range 4608).filter fun j => commutesA 276 hList[j]! yArr).length = 128 ∧
      (∀ k < 6, eqA 276 (compA 276 (genArr 3) (compA 276 (posArr (edgePairs.getD k ([], [])).1)
        (genArr 3))) (posArr (edgePairs.getD k ([], [])).2) = true) ∧
      eqA 276 (compA 276 bcbArr bcbArr) (idA 276) = true ∧
      eqA 276 (compA 276 bcbArr (compA 276 (genArr 0) bcbArr)) yArr = true ∧
      eqA 276 (compA 276 bcbArr (compA 276 yArr bcbArr)) (genArr 0) = true ∧
      eqA 276 (compA 276 bcbArr (compA 276 (genArr 2) bcbArr)) (genArr 2) = true ∧
      commutesA 276 kpArr (genArr 0) = true ∧ commutesA 276 kpArr yArr = true ∧
      eqA 276 (compA 276 kpArr kpArr) (idA 276) = true ∧ eqA 276 kpArr (idA 276) = false ∧
      eqA 276 (compA 276 uArr (compA 276 uArr uArr)) kpArr = true ∧
      ((List.range 630).any fun j => eqA 276 cBFS.1[j]! eaArr) = true := KernelLC.Co3Id.facts3094

end Certificates
