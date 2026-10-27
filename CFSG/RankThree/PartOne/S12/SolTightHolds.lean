module

public import CFSG.RankThree.PartOne.S12.SolInputs
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main

public section

namespace CFSG.RankThree.PartOne.SolIn

theorem solomonTimmesfeldTight_holds :
    CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight := by
  have hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models :=
    @CFSG.Milestones.cl_lit_classical_involution_theorem_models
  have hQuat : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie :=
    CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
      (CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
      (CFSG.CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
        CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
  exact solomonTimmesfeldTight_of_inputs
    (CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
      CFSG.ComponentClassification.Foote5.HallGen.hallQ8Residual)
    ⟨CFSG.CGT.PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz hCIT hQuat
        CFSG.CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate,
      CFSG.CGT.PushingUpLit.SolKR2.solomonTimmesfeldMainRankTwo_holds⟩

end CFSG.RankThree.PartOne.SolIn
