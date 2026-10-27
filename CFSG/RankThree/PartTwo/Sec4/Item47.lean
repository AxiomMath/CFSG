module

public import CFSG.RankThree.PartTwo.Sec4.Item47CasesExc
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem alt47_or_trialityD4
    (h46 : Item4_6) (hin : Inputs47NoD4) {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    {a : G} (ha : orderOf a = 3) (hout : InducesOuterTheta a L) :
    Alt47 L a ∨ ∃ f : ℕ,
      Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 f := by
  have ha3 : a ^ 3 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  rcases h46 G hG h3 L hL with ⟨p, e, _, hp2, he, he₁⟩ | ⟨p, e, _, hp3, he1, he2, h2⟩ |
    ⟨p, _, hp3, h3'⟩ | h4 | h5 | h6 | h7 | h8
  · obtain ⟨e₁⟩ := he₁
    exact Or.inl (alt47_of_psl2_odd hp2 he e₁ ha3 hout)
  · refine Or.inl ?_
    rcases h2 with h | he₁ | he₁
    · exact alt47_of_slThreeEps hp3 he1 he2 h ha3 hout
    · obtain ⟨e₁⟩ := he₁
      exact alt47_of_projSL_three hp3 he1 he2 e₁ ha3 hout
    · obtain ⟨e₁⟩ := he₁
      exact alt47_of_projSU_three hp3 he1 he2 e₁ ha3 hout
  · exact (false_of_list46_three hin hp3 h3' ha3 hout).elim
  · exact (false_of_list46_four hq h4 ha3 hout).elim
  · exact (false_of_list46_five hin hq h5 ha3 hout).elim
  · rcases h6 with (⟨n, hn, h⟩ | ⟨f, h⟩) | ⟨n, hn, h⟩
    · refine Or.inl ?_
      rcases h with he₁ | he₁ | he₁ | he₁ | he₁ <;> obtain ⟨e₁⟩ := he₁
      · exact alt47_of_psl2_even hn e₁ ha3 hout
      · exact alt47_of_projSL_three_even hG h3 hq hn e₁ ha3 hout
      · exact alt47_of_projSU_three_even hq hn e₁ ha3 hout
      · exact alt47_of_projSp_two_even hG h3 hq hn e₁ ha3 hout
      · exact (false_of_projSU_four_even hin hG h3 hq hn e₁ ha3 hout).elim
    · rcases h with h | h | h | h | h
      · exact Or.inl (alt47_of_g2_even hin hG h3 h ha3 hout)
      · exact Or.inr ⟨f, h⟩
      · exact Or.inl (alt47_of_suzuki h ha3 hout)
      · exact Or.inl (alt47_of_ree hin h ha3 hout)
      · exact (false_of_tits hin h ha3 hout).elim
    · exact Or.inl (alt47_of_slThreeEps_even hq hn h ha3 hout)
  · exact (false_of_list46_seven hin h7 ha3 hout).elim
  · exact (false_of_list46_eight hin hq h8 ha3 hout).elim

theorem rank3II_4_7_of
    (h46 : Item4_6) (hin : Inputs47) :
    Item4_7 := by
  intro G _ _ hG h3 L hL a ha hout
  rcases alt47_or_trialityD4 h46 hin.toNoD4 hG h3 hL ha hout with h | ⟨f, h⟩
  · exact h
  · exact alt47_of_trialityD4 hin hG h3 h (by rw [← ha, pow_orderOf_eq_one]) hout

theorem alt47W_of_trialityD4
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 f)
    (a : G) : Alt47W L a :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨f, h.1.2.1, h⟩)))

theorem rank3II_4_7W_of_noD4
    (h46 : Item4_6) (hin : Inputs47NoD4) : Item4_7W := by
  intro G _ _ hG h3 L hL a ha hout
  rcases alt47_or_trialityD4 h46 hin hG h3 hL ha hout with h | ⟨f, h⟩
  · exact h.toW
  · exact alt47W_of_trialityD4 h a

end CFSG.RankThree.PartTwo.Sec4
