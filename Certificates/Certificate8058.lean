module

public import Certificates.Data.K426J3
import Certificates.Kernel.K426.J3TFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
theorem certificate8058 :
    (linesOK3 3 243 13 6156 j3tCBGens j3tKeys j3tCBCert j3tLines = true ∧
      CFSG.Monster.B.Co2.Native.allLt 2 (fun c => validA 6156 j3tReps[c]! &&
        eqA 6156 (powArr 6156 j3tReps[c]! 3) (CFSG.Monster.B.Co2.Native.idA 6156)) = true ∧
      transOK2 13 6156 j3tTrans j3tReps j3tLines j3tRec PairJ3.levels PairJ3.baseArr = true ∧
      CFSG.Monster.B.Co2.Native.allLt 13 (fun j => decide (j3tRec.getD j 0 < 2)) = true) ∧
    (centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[0]! j3tRelsA j3tCAGens j3tKeys
        j3tCACert 1080 = true ∧
      centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[1]! j3tRelsB j3tCBGens j3tKeys
        j3tCBCert 243 = true) ∧
    (derivedLeOK 6156 j3tCAGens j3tDGens j3tKeys j3tDCert 360 = true ∧
      wordsOneOK 6156 j3tDGens j3tA6Rels = true ∧
      CFSG.Monster.B.Co2.Native.allLt 2 (fun l => siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tDGens[l]!) = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tG = true ∧
      detOK 6156 j3tDGens j3tG j3tWu j3tWv 1 = true) := KernelK426J3.facts

end Certificates
