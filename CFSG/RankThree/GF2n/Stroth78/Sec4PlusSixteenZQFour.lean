module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEightSmall
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltRow
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEightU33
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusNineSp
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusTenOmega
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEleven
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusTwelve
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusThirteenOmega
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFifteen
public import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenZQFour

public section

namespace CFSG.RankThree.GF2n.Stroth78

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}



theorem false_of_threeFourPlus_of_card_ZQ_eq_four
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w) (h34 : ThreeFourPlus S a)
    (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4)
    (hbG : ∃ b ∈ ZQ z, b ∉ Subgroup.zpowers z ∧ b ∈ commutator G) : False := by
  have h217 := stroth78_217_of_card_ZQ_eq_four S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa hZ
  rcases Xsub_lieModel_or_psu33_of_threeFourPlus S h h217 h34 with
    ⟨m, hm, hL⟩ | ⟨m, hm, hL⟩ | ⟨m, hm, hL⟩ | ⟨m, hm, hL⟩ | hL
  · rcases (show m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | h5
    · exact not_lieModel_psl_three_of_card_ZQ_eq_four S h h217 h34 hw4 hZ hL
    · exact not_lieModel_psl_four_of_card_ZQ_eq_four S h h217 h34 hw4 hZ hL hbG
    · exact not_lieModel_psl_of_card_ZQ_eq_four S h h217 h34 hZ h5 hL
  · rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | h5
    · exact not_lieModel_pOmegaPlus_four_of_card_ZQ_eq_four S h h217 h34 hZ hL
    · exact not_lieModel_pOmegaPlus_of_card_ZQ_eq_four S h h217 h34 hZ h5 hL
  · rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | h4
    · exact not_lieModel_psp_three_of_card_ZQ_eq_four S h h217 h34 hw4 hZ hL
    · exact not_lieModel_psp_of_card_ZQ_eq_four S h h217 h34 hZ h4 hL
  · exact not_lieModel_pOmegaMinus_of_card_ZQ_eq_four S h h217 h34 hZ hm hL
  · exact not_lieModel_psu33_of_card_ZQ_eq_four S h h217 h34 hw4 hZ hL

end CFSG.RankThree.GF2n.Stroth78
