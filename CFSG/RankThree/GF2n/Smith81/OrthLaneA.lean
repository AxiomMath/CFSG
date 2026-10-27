module

public import CFSG.RankThree.GF2n.Smith81.OrthFour
public import CFSG.RankThree.GF2n.Smith81.Orth216Odd

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def OrthNoA2E1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), Cfg M Q Z B →
    CtxD4 M Q Z B t → CaseE1 M Q Z B t → NoA2All M Q Z


theorem orthTacit_of_noA2E1 (hG : StrothGenByBStatement) (hE1 : OrthNoA2E1Statement) :
    OrthTacitStatement := by
  intro G _ _ M Q Z B hc B' hB'
  obtain ⟨t, ht, h1 | ⟨m, hm⟩⟩ := hc.orth
  · have hno : NoA2 Q Z (LB M Q B') := hE1 G M Q Z B t hc.toCfg ht h1 B'
      (by obtain ⟨g, hg⟩ := hB'.conj; exact ⟨g, hg⟩) hB'.le hB'.ne
    exact ⟨hno, hG G M Q Z B' hB' 4 h1.width (by norm_num) hno⟩
  · exact orthTacit_of_caseE2 hc.toCfg hm hG B' hB'

theorem smithLaneOrth_of_remaining (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hG : StrothGenByBStatement) (hTim : TimmesfeldOutcomeStatement)
    (h217 : Smith217Statement) (h28 : Smith28OrthStatement) (h212 : Smith212OrthCoreStatement)
    (h213 : Smith213OrthStatement) (h23 : Smith23E1LgenStatement)
    (h2 : Smith24ActE2TwoStatement) (hE1 : OrthNoA2E1Statement)
    (hInsp : Smith219OrthInspectionStatement) : LaneOrthStep :=
  have hT := orthTacit_of_noA2E1 hG hE1
  Smith216Odd.smithLaneOrth_of_28 hTim h28 h212 h213
    (smith24Act_of_four h34 h310 hG (smith24ActFour_of h23 h2))
    (smith52Act_of (smith25Orth_of_inputs h34 hT) hT) h217 hInsp

end CFSG.RankThree.GF2n.Smith81
