module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2Reduction
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5SmallONan
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4L227
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bL227
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5SmallJ3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6ZHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvergroupHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332THolds
public import CFSG.LocalAnalysis.UniquenessCase.UCK461Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Core
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1CoverHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6aHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6bHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega8Minus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSp6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K7Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

section


theorem uc_theorem_8_2_four_holds
    : CFSG.Yardstones.Mf4cdcdf2e013.Theorem82Four :=
  theorem82Four_of_inputs
    ⟨k1_holds, k2_of_k1 k1_holds k2Lie_holds, k3Exp_holds, k3Out_holds, k4a_holds,
        k4b_of_k4a k4a_holds,
      k5J3_holds, k5ONan_holds, k5U42_holds, k5L227_holds, k6a_holds, k6b_holds,
          k6c_of_facts
              ⟨SignedFacts.sp6K6cFacts_holds, SignedFacts.omega7K6cFacts_holds,
                  SignedFacts.omega8MinusK6cFacts_holds, SignedFacts.slK6cFacts_holds 6,
                  SignedFacts.suK6cFacts_holds 6, SignedFacts.slK6cFacts_holds 7,
                  SignedFacts.suK6cFacts_holds 7⟩,
      k6dL4_holds, k6r_of_facts
          ⟨SignedFacts.sp6K6rFacts_holds, SignedFacts.omega7K6rFacts_holds,
              SignedFacts.omega8MinusK6rFacts_holds, SignedFacts.slK6rFacts_holds 6,
              SignedFacts.suK6rFacts_holds 6, SignedFacts.slK6rFacts_holds 7,
              SignedFacts.suK6rFacts_holds 7⟩, k6L4_holds, k6ZL4_holds, k7_holds⟩
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.stronglyEmbeddedSolvable_holds
    UCK.k332ThreeAb_holds (perfectAutInner_of_schreier CFSG.AGLEmbedding.kFactCatalogSchreier_holds) UC22.InS3.UC326.k326P2S_holds k11_holds
    UCK.k32_holds CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.asc81bNineThree_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalCGTBlock_proved l3NotEvenClassical_holds
    l3EvenParabolic_holds UCK.k461_holds UCK.k462_holds UC22.InS3.UC49.k49I_core49
    (CGT.PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz
        CFSG.Milestones.cl_lit_classical_involution_theorem_models
        (CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
            (CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
                CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
            (CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
                CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))
        CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate)
    l3Overgroup_holds

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
