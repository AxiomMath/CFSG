module

public import CFSG.RankThree.GF2n.Smith81.OrthLaneClosed
public import CFSG.RankThree.GF2n.Tim81.RonanInputsHolds

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section E1


theorem Smith23E1.smith23E1Lgen_holds : Smith23E1LgenStatement := by
  have h34 := stroth34Statement_unconditional
  have h310 := stroth310Statement_unconditional
  have hNt := strothNtStatement_unconditional
  have h44 := stroth44Statement_unconditional
  exact smith23E1Lgen_of_remaining2 h34 h310 hNt h44 strothGenByBStatement_certified
    (CFSG.Walter.walter_modelsForm_of_lemma65_base CFSG.Walter.W67.lemma_6_5
      CFSG.Walter.Ree.T2.baseExists)
    KFacts.walterListLargeSylow_holds
    (caseA2_closed (corollaryBStmt_of_theoremAStmt theoremAStmt_holds) h34 h310 hNt h44)
    listNoPerfectOut_holds

theorem smith28Orth_holds : Smith28OrthStatement := by
  have hG := strothGenByBStatement_certified
  have hT := orthTacit_of_noA2E1 hG orthNoA2E1Statement_holds
  exact smith28Orth_of_remaining stroth34Statement_unconditional
    stroth310Statement_unconditional strothNtStatement_unconditional hG
    Smith23E1.smith23E1Lgen_holds (FourPlus.orthSimFourPlus_of hT) (orthR0HypFour_of hT)
    (orthDTHypFour_of (smith52Act_of (smith25Orth_of_inputs stroth34Statement_unconditional hT)
      hT) hT)

theorem smith216Orth_holds : Smith216OrthStatement := by
  have h34 := stroth34Statement_unconditional
  have h310 := stroth310Statement_unconditional
  have hNt := strothNtStatement_unconditional
  have hG := strothGenByBStatement_certified
  have h23 := Smith23E1.smith23E1Lgen_holds
  have h28 := smith28Orth_holds
  have hT := orthTacit_of_noA2E1 hG orthNoA2E1Statement_holds
  have h24 := smith24Act_of_23 h34 h310 hNt hG h23
  have h25 := smith25Orth_of_inputs h34 hT
  have h52 := smith52Act_of h25 hT
  have h4 := orth212C4Cond_of_root (orth212C4Root_of h24 h52) h28
  have hK := orthClass_of h25 h52 h28 h4
  have h5 := orth212C5Cond_of h24 h28 h4 hK
  exact Smith216Odd.smith216Orth_of_28 h28
    (smith212OrthCore_of_remaining h34 h310 hNt hG h23 h28 h5)
    (smith213Orth_of_parts (orth213Elem_of h24 hK)
        (orth213Outside_of (orth213Frame_of (orth213Elem_of h24 hK))
            (orth213Odd_of h24 hK h28 h4 (orth212C7Cond_of_C4 h4 h28) h5)))
    (smith216OrthCount_of_52Act h24 h52)

end E1

section Lane


theorem smithLaneOrth_holds : LaneOrthStep :=
  smithLaneOrth_closed (corollaryBStmt_of_theoremAStmt theoremAStmt_holds)

end Lane

end CFSG.RankThree.GF2n.Smith81
