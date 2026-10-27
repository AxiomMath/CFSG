module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofCases
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPSL2
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPGU
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPSL3
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item82Proof CFSG.RankThree.PartTwo.Sec8.Item83Proof

theorem item82TwoList_of
    (h45 : Sec4.Item4_5) (h47 : Sec4.Item4_7) (hKind : KF82TwoLThreeKinds)
    (hOdd : KF82OddSLThree) (hR1 : Item82TwoSLThree) (hR2 : Item82TwoPSL2Three) :
    Item86ResProof.Item82TwoList := by
  intro G _ _ A c L a h h81
  have hAN := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp
    h.mem_partTwoF.1 h.mem_A h.ne_one L h.mem_thetaComponentsAt
  exact isList82Two_of_alt47 h h81 hAN kF82TwoNoE9PSL2 kF82TwoNoE9PGU kF82TwoPSL3Odd hKind hOdd
    hR1 hR2
    (Item82OneProof.alt47_of_hyp81 h47 h)

theorem item82Two_of_kfacts
    (h611 : Sec6.Item6_11_1) (h45 : Sec4.Item4_5) (h47 : Sec4.Item4_7)
    (hKind : KF82TwoLThreeKinds) (hOdd : KF82OddSLThree) (hR1 : Item82TwoSLThree)
    (hR2 : Item82TwoPSL2Three) : Item82Two :=
  Item86ResProof.item82Two_of h611 (item82TwoList_of h45 h47 hKind hOdd hR1 hR2)

end CFSG.RankThree.PartTwo.Sec8
