module

public import Certificates.Data.K426J3
import Certificates.Kernel.SporSch.J3K426.Glue
import Certificates.Kernel.SporSch.J3K426.C5170

public section

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.KC.BfsPin CFSG.KC.PkPow CertificateChecks.KernelSporSch.J3KT

namespace Certificates

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426 in
theorem certificate5170 : CFSG.RankThree.Native.commA 6156 j3tLines[4]! j3tReps[1]! = true ∧ eqA 6156 j3tLines[4]! j3tReps[1]! = false ∧
    eqA 6156 j3tLines[4]! (powArr 6156 j3tReps[1]! 2) = false := by
  have pL : PP 6156 13 (L 4) := ppL (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [commA, hL (by norm_num), hX1, compA_PP pL ppX1, compA_PP ppX1 pL,
      eqA_PP (pL.mul ppX1) (ppX1.mul pL)]
    exact comm5170
  · rw [hL (by norm_num), hX1, eqA_PP pL ppX1]
    exact not_of_bIf ne5170
  · rw [hL (by norm_num), hX1, (pow_eq ppX1 2).1, eqA_PP pL (pow_eq ppX1 2).2]
    exact not_of_bIf ne5170sq

end Certificates
