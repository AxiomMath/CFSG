module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import Certificates.Kernel.RuThree.Facts
public import CFSG.RankThree.PartOne.KS.PKit

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
theorem certificate24946 :
    caseChainOK2P 4060 ruThreeArrs ruThreeBaseArr ruThreeWords (ruArr4060 0) (ruArr4060 1) =
        true ∧
      rawOrbitSizes 4060 ruThreeArrs ruThreeBaseArr = [4060, 2304, 650, 8, 3, 1, 1] ∧
      validA 4060 (ruArr4060 0) = true ∧ validA 4060 (ruArr4060 1) = true ∧
      centOKP 3 4060 ruThreeArrs ruThreeBaseArr ruThreeLines[0]! ruThreeRels ruThreeC0Gens
        ruThreeKeys ruThreeC0Cert 2160 = true ∧
      eqA 4060 ruThreeC0Gens[0]! ruThreeLines[0]! = true ∧
      ruThreeInvOK = true := KernelRuThree.ok24946

end Certificates
