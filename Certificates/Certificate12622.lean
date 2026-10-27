module

public import Certificates.Data.K426J3
import Certificates.Kernel.SporSch.J3K426.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
theorem certificate12622 :
    eqA 6156 (compA 6156 j3tG j3tReps[0]!) (compA 6156 (compA 6156 j3tReps[0]! j3tReps[0]!) j3tG) =
        true ∧
      eqA 6156 (compA 6156 (compA 6156 j3tG j3tDGens[0]!) (compA 6156 j3tG j3tDGens[0]!))
        (CFSG.Monster.B.Co2.Native.idA 6156) = true := KernelSporSch.J3KT.facts12622

end Certificates
