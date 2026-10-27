module

public import CFSG.RankThree.PartOne.S12.FinalRemaining
public import CFSG.RankThree.PartOne.Outcome.Dichotomy

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem part_one_outcome_of_remaining
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hQL : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : KProper InCatalog G) (hchar : IsCharTwoType G) (he : evenRank G = 3)
    (hq : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3) :
    IModel G ∨ AschCoreLocal G 2 :=
  part_one_outcome_of Outcome.selectedPrimeDichotomy_of_remaining
    (vanishingRecognition_of_remaining hCIT hQL) G hnonab hK hchar
    he hq

end CFSG.RankThree.PartOne
