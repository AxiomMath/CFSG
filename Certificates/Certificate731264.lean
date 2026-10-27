module

public import Certificates.Data.KD4BU38.Data
import Certificates.Kernel.U38.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes CFSG.RankThree.PartTwo.Sec4.Item434U38
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu in
theorem certificate731264 :
    (CFSG.RankThree.Native.enumOK 513 pgu38SylowGens pgu38Key (pgu38SylowEnum ()) = true ∧
      (pgu38SylowEnum ()).pts.size = 243) ∧
    allLt 3 (fun j => pgu38SiftX (compA 513 pgu38SylowGens[j]!
      (powArr 513 (invCand 513 gensO[7]!) pgu38SylowExp[j]!))) = true ∧
    pgu38ClassCheck (pgu38SylowEnum ()).pts = true ∧
    allLt 10 (fun j => validA 513 pgu38ClassReps[j]! && validA 513 pgu38RepConj[j]! &&
      pgu38SiftX (compA 513 pgu38RepConj[j]!
        (powArr 513 (invCand 513 gensO[7]!) pgu38RepConjExp[j]!)) &&
      (List.range 5).any fun r => decide (pgu38RepIdx[r]! < 10) &&
        eqA 513 (conjA 513 pgu38RepConj[j]! pgu38ClassReps[j]!)
          pgu38ClassReps[pgu38RepIdx[r]!]!) = true ∧
    allLt 5 (fun r => decide (pgu38RepIdx[r]! < 10) && validA 513 pgu38FrobConj[r]! &&
      pgu38SiftX (compA 513 pgu38FrobConj[r]!
        (powArr 513 (invCand 513 gensO[7]!) pgu38FrobConjExp[r]!)) &&
      (eqA 513 (conjA 513 pgu38FrobConj[r]! (conjA 513 gensO[8]! pgu38ClassReps[pgu38RepIdx[r]!]!))
          pgu38ClassReps[pgu38RepIdx[r]!]! ||
        eqA 513 (conjA 513 pgu38FrobConj[r]! (conjA 513 gensO[8]! pgu38ClassReps[pgu38RepIdx[r]!]!))
          (invCand 513 pgu38ClassReps[pgu38RepIdx[r]!]!))) = true ∧
    pgu38SiftX (powArr 513 gensO[7]! 3) = true ∧
    pgu38SiftX (compA 513 (conjA 513 gensO[8]! gensO[7]!) (powArr 513 (invCand 513 gensO[7]!) 2)) =
      true ∧
    pgu38SiftX (compA 513 (conjInvA 513 gensO[8]! gensO[7]!)
      (powArr 513 (invCand 513 gensO[7]!) 2)) = true := KernelU38.facts

end Certificates
