module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolSeven
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
import CFSG.RankThree.PartOne.S12.SolInputs
import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main
import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

theorem lit316SolomonSeven_of_cit'
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hL : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie) : Lit316SolomonSeven :=
  lit316SolomonSeven_of_tight
    (CFSG.RankThree.PartOne.SolIn.solomonTimmesfeldTight_of_inputs
      (CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
        CFSG.ComponentClassification.Foote5.HallGen.hallQ8Residual)
      (⟨CFSG.CGT.PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz hCIT hL
          CFSG.CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate,
        CFSG.CGT.PushingUpLit.SolKR2.solomonTimmesfeldMainRankTwo_holds⟩ :
        CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainResidue))

theorem lit316SolomonSeven_of_citMilestone :
    Lit316SolomonSeven :=
  lit316SolomonSeven_of_cit' @CFSG.Milestones.cl_lit_classical_involution_theorem_models
    (CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
      (CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
      (CFSG.CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))

end CFSG.RankThree.PartTwo.Sec19.SolSeven
