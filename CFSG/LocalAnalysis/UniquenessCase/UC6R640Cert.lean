module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R640
public import CFSG.CGT.PushingUpLit.CGT6.NineContentNormal
public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail6
public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.CGT.Timmesfeld75.FinalNodeRest
public import CFSG.HardMathSupport.Foote.Coordinator.Downstream
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.CGT.PushingUpLit CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem pushingUpCorollaryΩ_of_twoK_solK
    (u2 : AschbacherTheoremTwoK) (s25 : SolomonAlternatingBlockK) : PushingUpCorollaryΩ :=
  CFSG.CGT.PushingUpLit.CGT6.pushingUpCorollaryΩ_of_core
    (CFSG.CGT.PushingUpLit.CGT6.aschbacherSixThreeCore_of_embeddingK
      CFSG.HardMathSupport.Foote.Coordinator.aschbacherEmbeddingK_proved)
    (CFSG.CGT.PushingUpLit.CGT6.aschbacherNineContent_of_sixFourCore_noSixThree
      CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
      (CFSG.CGT.PushingUpLit.CGT6.aschbacherSixFourCore_of_hyps
        (CFSG.CGT.Timmesfeld75.simpleCaseListStmt_final_rest
          ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)
        CFSG.CGT.Timmesfeld75.lemma215 CFSG.CGT.Timmesfeld75.listWCIdentification_of_cert))
    u2 s25

theorem r6_40_1_holds
    (u2 : AschbacherTheoremTwoK) (s25 : SolomonAlternatingBlockK) (D : Data G) : R6_40_1 D :=
  r6_40_1_of_inputs CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved u2 s25 D

theorem r6_40_2_holds
    (u2 : AschbacherTheoremTwoK) (s25 : SolomonAlternatingBlockK) (D : Data G) : R6_40_2 D :=
  r6_40_2_of_pushingUp (pushingUpCorollaryΩ_of_twoK_solK u2 s25) D

end CFSG.LocalAnalysis.UniquenessCase.UC6
