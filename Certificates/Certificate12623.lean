
module

public import Certificates.Certificate12623Base

import Certificates.Kernel.SporSch.J3K426.Sift

public section

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
theorem certificate12623 :
    eqA 6156 (compA 6156 j3tLines[2]! j3tLines[4]!) (compA 6156 j3tLines[4]! j3tLines[2]!) = true ∧
      eqA 6156 (compA 6156 j3tLines[2]! j3tLines[0]!) (compA 6156 j3tLines[0]! j3tLines[2]!) = true ∧
      eqA 6156 (compA 6156 j3tLines[4]! j3tLines[0]!) (compA 6156 j3tLines[0]! j3tLines[4]!) = true ∧
      (List.range 27).all (fun m => decide (m = 0) ||
        decide (j3fix (j3e27Elt m) = if m % 3 = 0 then 0 else 36)) = true ∧
      (List.range 27).all (fun m => (List.range m).all fun m' =>
        !eqA 6156 (j3e27Elt m) (j3e27Elt m')) = true ∧
      decide (j3fix j3tReps[0]! = 36) = true ∧ decide (j3fix j3tReps[1]! = 0) = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tLines[2]! = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tLines[4]! = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tLines[0]! = true := KernelSporSch.J3KT.facts12623

end Certificates
