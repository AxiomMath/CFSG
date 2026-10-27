module

public import Certificates.Data.K426J3
import CFSG.Certificates.Kernel.BfsPinSetSound
import Certificates.Kernel.SporSch.J3K426.Glue
import Certificates.Kernel.SporSch.J3K426.C5172

public section

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PkPow
  CertificateChecks.KernelSporSch.J3KT

namespace Certificates

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426 in
theorem certificate5172 : validA 6156 j3tTrans[4]! = true ∧
    eqA 6156 (compA 6156 j3tTrans[4]! j3tLines[4]!)
      (compA 6156 (compA 6156 j3tReps[1]! j3tLines[4]!) j3tTrans[4]!) = true := by
  have hT : j3tTrans[4]! = unpack 6156 13 (F 24) := by
    rw [j3tTrans, getElem!_pos _ 4 (by simp), Array.getElem_ofFn]
    exact arr (by norm_num)
  have pT : PP 6156 13 (F 24) := pp (by norm_num)
  have pL : PP 6156 13 (L 4) := ppL (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hT]
    exact validA_unpack (CFSG.KS.Raw.Orb.allN_iff.1 perm 24 (by norm_num))
  · rw [hT, hL (by norm_num), hX1, compA_PP pT pL, compA_PP ppX1 pL, compA_PP (ppX1.mul pL) pT,
      eqA_PP (pT.mul pL) ((ppX1.mul pL).mul pT)]
    exact c5172

end Certificates
