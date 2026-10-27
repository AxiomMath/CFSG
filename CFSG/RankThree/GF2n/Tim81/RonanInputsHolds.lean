module

public import CFSG.RankThree.PartOne.S12.PushingUpOfCIT
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs

public section

namespace CFSG.CGT.Timmesfeld75

theorem theoremAStmt_holds :
    TheoremAStmt :=
  theoremA_final_rest ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩

end CFSG.CGT.Timmesfeld75

namespace CFSG.RankThree.PartOne

theorem pushingUpCorollary_holds :
    PushingUpCorollary :=
  pushingUpCorollary_of_cit_lie
    (CFSG.CGT.PushingUpLit.SolKNA.classicalInvolutionTheoremModels_of_citInputs
      CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
    (CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
      (CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
      (CFSG.CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))

end CFSG.RankThree.PartOne
