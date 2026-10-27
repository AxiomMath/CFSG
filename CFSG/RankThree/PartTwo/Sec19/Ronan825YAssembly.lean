module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
public import CFSG.RankThree.PartTwo.Sec19.RonanStep1915WHolds
public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofCore
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplit
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofWide3S1917
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofZ2
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSubfield
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofWire
import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoFinal
import CFSG.RankThree.PartTwo.Sec19.RonanTrialityE27Gen
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.Sec4.T444.Step452Residual
import CFSG.RankThree.PartTwo.Sec4.Item4442Proof
import CFSG.RankThree.PartTwo.KFacts.KS18OuterMain

public section

namespace CFSG.RankThree.PartTwo.Sec19.Ronan825Y

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section SplitLie

theorem step1919CoreSplitLie_holds : Step1919CoreSplitLie :=
  Step1915WProof.step1919CoreSplitLie_of_rest Item19Res2Proof.step1919CoreSplitLieRest

end SplitLie

section XGen

theorem ks1917XGen_holds : KS1917XGen :=
  ks1917XGen_of_seitzField_triality seitzThreeLThreePiField_holds
    (RonanSeitz199.seitzThreeTriality_of_odd
      LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.trialityThreePlanesOdd_holds)
    RonanTrialityE27Gen.trialityE27Gen_holds

end XGen

section Steps

theorem step1917_of_step1913
    (h1913 : Step1913) (h434 : Sec4.Item4_34Sec)
    (h131 : Sec13.Item131) (h194 : Item194UsedWide3) : Step1917 :=
  have h45 := Sec4.rank3II_4_5
  have h48 := Sec4.rank3II_4_8_of h45
  have h4441 := Sec4.rank3II_4_44_1_of_item4_34 h434 h45
  have h4442 := Sec4.rank3II_4_44_2_of h45 h434
  have hcen := step1917EqCentral_of h1913 (census1915_of_rowsS Sec4.RonanK429.k429RowsS_holds
      (Sec4.Item41Narrow.item4_1LargePrime_of_griess
          CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
      (PartOne.Mult.exceptionalCenterSmallPrimes_of_griess
          CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)) ks1917XGen_holds
  step1917_of_W_wide3 h1913 (Sec18.rank3II_18_1_1_of h4441)
    (Sec18.rank3II_18_1_2_of h4442 KFacts.KS18.ks18OuterInvolution) h194
    (step1915W_of_step1913 h1913) (Item19ResProof.step1917Z2W_of_step1913 h1913)
    (step1917J_of h1913 (step1917JPar_of h1913 h131 Item19Res2Proof.ksJParSubfield))
    (step1917Push_of h1913 h45 h48 (step1917PushEq_of h1913 (census1915_of_rowsS
        Sec4.RonanK429.k429RowsS_holds
        (Sec4.Item41Narrow.item4_1LargePrime_of_griess
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
        (PartOne.Mult.exceptionalCenterSmallPrimes_of_griess
            CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)) hcen))
    (step1917Lift_of h1913 h45 h48 (step1917LiftEq_of h1913 (census1915_of_rowsS
        Sec4.RonanK429.k429RowsS_holds
        (Sec4.Item41Narrow.item4_1LargePrime_of_griess
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
        (PartOne.Mult.exceptionalCenterSmallPrimes_of_griess
            CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)) hcen))

end Steps

end CFSG.RankThree.PartTwo.Sec19.Ronan825Y
