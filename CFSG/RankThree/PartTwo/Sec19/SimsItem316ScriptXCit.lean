module

public import CFSG.RankThree.PartTwo.Sec19.SimsSectionalTwoRankFour
public import CFSG.RankThree.PartTwo.Sec19.F194Item316XCit
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection

public section

namespace CFSG.RankThree.PartTwo.Sec19

theorem item316ScriptX_of_cit'
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hL : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie) : Item316ScriptX :=
  item316ScriptX_of_cit hCIT hL sectionalTwoRankFourCatalog_holds

theorem item316ScriptX_of_citMilestone :
    Item316ScriptX :=
  item316ScriptX_of_cit' @CFSG.Milestones.cl_lit_classical_involution_theorem_models
    (CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
      (CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
      (CFSG.CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))

end CFSG.RankThree.PartTwo.Sec19
