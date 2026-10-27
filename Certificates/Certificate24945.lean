module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import Certificates.Kernel.RuThree.QFacts
public import CFSG.RankThree.PartOne.KS.PKit

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
theorem certificate24945 :
    linesOKG 3 27 13 4060 ruThreeQGens ruThreeKeys ruThreeQCert ruThreeLines = true ∧
      CFSG.Monster.B.Co2.Native.allLt ruThreeQGens.size
        (fun l => siftA 4060 ruThreeLevels ruThreeBaseArr 0 ruThreeQGens[l]!) = true ∧
      transOKG 13 4060 ruThreeTransporters ruThreeLines ruThreeRec ruThreeLevels
        ruThreeBaseArr = true ∧
      CFSG.Monster.B.Co2.Native.allLt 13 (fun j => (List.range 1).any fun i => ruThreeRec.getD j 0 == i) = true ∧
      ruThreeRec.getD 0 0 = 0 := KernelRuThree.ok24945

end Certificates
