module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434Out
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434Small
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoFinal
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4NoninnerTwo
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactCore
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofWire
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4ThreeProved
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434OmegaMinus
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48TwentySeven
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Inner
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28TwentySeven
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Outer
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Proof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pOuter
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Proof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherEasy
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL28
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL264
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL52
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL72
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL44
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSp44
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSp64
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU44
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU42
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG24
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTits
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38K0
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof CFSG.LieType.SeitzGeneration

section CertsD4Two


theorem seitz199D4Two_of_char2
    (hS : SeitzPlanes fun d p _ => p = 3 ∧ IsTrialityIndex d.1 ∧ d.1.characteristic = 2) :
    Seitz199D4Two := by
  intro X _ _ D hD3 hD9 ⟨f, hmod⟩
  exact closure_fixSet_of_trialityD4_char2 hS hmod D
    (Item19ResProof.isElemAbelian_of_pow_three hD3 hD9) hD9

end CertsD4Two

section CertsD4Leaves


theorem seitz199D4Two_of_leaves (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) : Seitz199D4Two :=
  seitz199D4Two_of_char2 (seitzThreeTrialityChar2_of hT hA
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcOuterNarrowTrialityThree_proved)

end CertsD4Leaves

section CertsL3Holds


theorem seitz199L3_holds : Seitz199L3 :=
  seitz199L3_of_seitzThree
    (seitzThreeLThreePi_of_field seitzThreeLThreePiField_holds)
    (seitz199Outer_of_seitzField_diag seitzThreeLThreePiField_holds
      seitz199OuterUnitaryDiag_holds)

end CertsL3Holds

section Certs434


theorem seitz434_of_seitzFieldTwo (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) (h27 : Seitz434RestTwentySeven) : Seitz434 :=
  seitz434_of_narrow_scopes
    (seitzThreePartTwoChar2_of seitzThreeLThreePiFieldTwo_holds seitzThreeSec441NoninnerTwo_holds
      hT hA CFSG.LieType.SeitzGeneration.seitzExcAnisotropicReeF4Three_holds)
    (seitzThreeLThreePi_of_field seitzThreeLThreePiField_holds) seitz199L3_holds
    (seitz199D4Two_of_leaves hT hA)
    (seitzThreeOddInner_of seitzThreeSec441Inner seitzThreeG2Inner)
    oddPrimeFieldPlanesInner_holds h27

end Certs434

section CertsItem


theorem item434SmallTwo_of_leaves (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) (h27 : Seitz434OtherTwentySeven) :
    Item434SmallTwo :=
  item434SmallTwo_of item434OmegaMinusEight
    (item434SmallTwoIII_of_parts item434SmallTwoIII_Sp62
      (item434SmallTwoIII_Sp48_of item434SmallTwoIII_Sp48_27)
      (item434SmallTwoIII_G28_of item434SmallTwoIII_G28_9Inner item434SmallTwoIII_G28_27)
      (item434SmallTwoIII_D42_of_narrow (seitz199D4Two_of_leaves hT hA)
        item434SmallTwoIII_D42_27))
    (item434SmallTwoIV_of
      (Census.tripleCoverLie_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
      item434SmallTwoIV_U62_27 item434SmallTwoIV_O8p_27Outer item434SmallTwoIV_F42_27
      item434SmallTwoIV_U48_27)
    (item434SmallTwoOther_of_parts item434SmallTwoOtherAtL28 item434SmallTwoOtherAtL264
        item434SmallTwoOtherAtU34 item434SmallTwoOtherAtSp42 item434SmallTwoOtherAtSp44
        item434SmallTwoOtherAtU42 item434SmallTwoOtherAtU44 item434SmallTwoOtherAtG22
        item434SmallTwoOtherAtG24 item434SmallTwoOtherAtTits item434SmallTwoOtherAtL52
        item434SmallTwoOtherAtL62 item434SmallTwoOtherAtL72 item434SmallTwoOtherAtL44
        item434SmallTwoOtherAtSp64 item434SmallTwoOtherAtU54
        (item434OtherL3Pi_of_narrow seitz199L3_holds
            (seitzL3PiGap_of_seitzField seitzThreeLThreePiField_holds) seitzL3SixtyFour_holds
            Item434U38.item434OtherU38TwentySeven_of_certificates)
        (item434SmallTwoOtherAtField_of
            (seitz434Other_of_seitzFieldTwo seitzThreeLThreePiFieldTwo_holds
                seitzThreeSec441NoninnerTwo_holds hT hA
                CFSG.LieType.SeitzGeneration.seitzExcAnisotropicReeF4Three_holds h27)))

end CertsItem

end CFSG.RankThree.PartTwo.Sec4
