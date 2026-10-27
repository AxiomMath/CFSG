module

public import CFSG.RankThree.PartOne.S12.PartOneRemaining
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieWiredQCW

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open CFSG.ClassicalInvolution.MilestoneAssembly

theorem part_one_outcome_of_citInputs
    (h : CFSG.CGT.PushingUpLit.SolKNA.CITInputs)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : KProper InCatalog G) (hchar : IsCharTwoType G) (he : evenRank G = 3)
    (hq : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3) :
    IModel G ∨ AschCoreLocal G 2 :=
  part_one_outcome_of_remaining
    (CFSG.CGT.PushingUpLit.SolKNA.classicalInvolutionTheoremModels_of_citInputs h)
    (CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
      (CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs h)
      (CFSG.CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs h))
    G hnonab hK hchar he hq

theorem part_one_outcome_of_qcw19
    (h : CFSG.ComponentClassification.QuaternionComponent.WiredInputs₁₉)
    (hr4 : CFSG.ClassicalInvolution.GH74SectionalModels → CFSG.ClassicalInvolution.Q3.TightR4)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : KProper InCatalog G) (hchar : IsCharTwoType G) (he : evenRank G = 3)
    (hq : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3) :
    IModel G ∨ AschCoreLocal G 2 :=
  part_one_outcome_of_citInputs
    (CFSG.CGT.PushingUpLit.SolKNA.citInputs_of_qcw19 h hr4) G hnonab hK hchar he hq

end CFSG.RankThree.PartOne
