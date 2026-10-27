
module

public import Certificates.Certificate12624Base

import Certificates.Kernel.SporSch.J3K426.Glue

public section

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
theorem certificate12624 :
    eqA 6156 (powArr 6156 (evalWA 6156 j3tDGens j3tWu) 3) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
      eqA 6156 (powArr 6156 (evalWA 6156 j3tDGens j3tWv) 3) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
      (List.range 9).all (fun m => (List.range m).all fun m' =>
        !eqA 6156 (j3uvElt m) (j3uvElt m')) = true ∧
      (List.range 9).all (fun m => decide (m = 0) || decide (j3fix (j3uvElt m) = 0)) = true := KernelSporSch.J3KT.facts12624

end Certificates
