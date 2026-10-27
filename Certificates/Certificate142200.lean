module

public import Certificates.Data.K426J3
import Certificates.Kernel.SporSch.J3K426.Glue
import Certificates.Kernel.SporSch.J3K426.C142200

public section

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.KC.BfsPin CFSG.KC.PkPow CertificateChecks.KernelSporSch.J3KT

namespace Certificates

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native in
theorem certificate142200 :
    eqA 6156 (CFSG.RankThree.Native.conjA 6156 j3tG j3tReps[0]!) (powArr 6156 j3tReps[0]! 2) = true ∧
      eqA 6156 (powArr 6156 (evalWA 6156 j3tDGens j3tWu) 3) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
      eqA 6156 (evalWA 6156 j3tDGens j3tWu) (CFSG.Monster.B.Co2.Native.idA 6156) = false ∧
      eqA 6156 (evalWA 6156 j3tDGens j3tWv) (CFSG.Monster.B.Co2.Native.idA 6156) = false ∧
      eqA 6156 (evalWA 6156 j3tDGens j3tWv) (evalWA 6156 j3tDGens j3tWu) = false ∧
      eqA 6156 (evalWA 6156 j3tDGens j3tWv) (powArr 6156 (evalWA 6156 j3tDGens j3tWu) 2) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjA, hG, hX0, invCand_PP ppG, compA_PP ppX0 ppG.inv, compA_PP ppG (ppX0.mul ppG.inv),
      (pow_eq ppX0 2).1, eqA_PP (ppG.mul (ppX0.mul ppG.inv)) (pow_eq ppX0 2).2]
    exact conj142200
  · rw [hU.1, (pow_eq hU.2 3).1, idA_eq szOK', eqA_PP (pow_eq hU.2 3).2 (PP.id szOK')]
    exact u3
  · rw [hU.1, idA_eq szOK', eqA_PP hU.2 (PP.id szOK')]
    exact not_of_bIf uNe142200
  · rw [hV.1, idA_eq szOK', eqA_PP hV.2 (PP.id szOK')]
    exact not_of_bIf vNe142200
  · rw [hV.1, hU.1, eqA_PP hV.2 hU.2]
    exact not_of_bIf vu142200
  · rw [hV.1, hU.1, (pow_eq hU.2 2).1, eqA_PP hV.2 (pow_eq hU.2 2).2]
    exact not_of_bIf vu2142200

end Certificates
