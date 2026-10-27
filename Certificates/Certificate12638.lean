module

public import Certificates.Data.K426J3
import Certificates.Kernel.SporSch.J3K426.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
theorem certificate12638 : CFSG.Monster.B.Co2.Native.allLt 2 (fun l => eqA 6156 (compA 6156 j3tReps[0]! j3tDGens[l]!)
    (compA 6156 j3tDGens[l]! j3tReps[0]!)) = true := KernelSporSch.J3KT.facts12638

end Certificates
