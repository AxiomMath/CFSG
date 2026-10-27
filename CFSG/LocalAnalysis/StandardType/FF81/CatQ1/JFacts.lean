module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.PRankBound
public import CFSG.RankThree.PartTwo.Sec21.FF79KOneTwo
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

@[expose] public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open CFSG.Open.StatedAPI CFSG.RankThree.PartTwo.Sec21.FF79

private theorem statedClassicalModel_top_of_modelJ {J : Type} [Group J] {n : ℕ}
    (h : StatedClassicalModel J .PSL n 2 1) :
    StatedClassicalModel (⊤ : Subgroup J) .PSL n 2 1 := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨e⟩⟩ := h
  exact ⟨hadm, K, hK, hfin, hcard, ⟨Subgroup.topEquiv.trans e⟩⟩

private theorem center_eq_bot_of_simple_aux {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
  · exact h0
  · exfalso
    have : IsMulCommutative S :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a)⟩⟩
    exact h (Group.is_simple_iff_prime_card.1 inferInstance)

theorem twentyThousand_dvd_card_of_modelJ (J : Type) [Group J] [Finite J]
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) :
    20160 ∣ Nat.card J := by
  rcases hJ with h4 | h5
  · rw [card_of_statedClassicalModel_psl_four_two h4]
  · rw [card_of_statedClassicalModel_psl_five_two h5]
    norm_num

theorem not_twentySeven_dvd_card_of_modelJ (J : Type) [Group J] [Finite J]
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) :
    ¬ 27 ∣ Nat.card J := by
  rcases hJ with h4 | h5
  · rw [card_of_statedClassicalModel_psl_four_two h4]
    decide
  · rw [card_of_statedClassicalModel_psl_five_two h5]
    decide

theorem orderOf_ne_nine_of_modelJ (J : Type) [Group J] [Finite J]
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) (x : J) :
    orderOf x ≠ 9 := by
  intro hx9
  rcases hJ with h4 | h5
  · have hX : IsLnq 4 2 1 (⊤ : Subgroup J) := statedClassicalModel_top_of_modelJ h4
    have hSyl := (ff79_1_2_four J hX).1
    have hx_pgroup : IsPGroup 3 (Subgroup.zpowers x) := by
      rw [IsPGroup.iff_card]
      use 2
      rw [Nat.card_zpowers, hx9]
      norm_num
    obtain ⟨P, hxP⟩ := hx_pgroup.exists_le_sylow
    have hxP' : x ∈ (P : Subgroup J) := hxP (Subgroup.mem_zpowers x)
    have hElem := hSyl P
    have hx3 : x ^ 3 = 1 := by
      have hxp : (⟨x, hxP'⟩ : P) ^ 3 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hElem.1.exponent_dvd_p (⟨x, hxP'⟩ : P)
      have := congrArg (fun y : P => (y : J)) hxp
      simpa using this
    have hx3_ne : x ^ 3 ≠ 1 := by
      intro h
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h
      rw [hx9] at hdvd
      norm_num at hdvd
    exact hx3_ne hx3
  · have hX : IsLnq 5 2 1 (⊤ : Subgroup J) := statedClassicalModel_top_of_modelJ h5
    have hSyl := (ff79_1_2_five J hX).1
    have hx_pgroup : IsPGroup 3 (Subgroup.zpowers x) := by
      rw [IsPGroup.iff_card]
      use 2
      rw [Nat.card_zpowers, hx9]
      norm_num
    obtain ⟨P, hxP⟩ := hx_pgroup.exists_le_sylow
    have hxP' : x ∈ (P : Subgroup J) := hxP (Subgroup.mem_zpowers x)
    have hElem := hSyl P
    have hx3 : x ^ 3 = 1 := by
      have hxp : (⟨x, hxP'⟩ : P) ^ 3 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hElem.1.exponent_dvd_p (⟨x, hxP'⟩ : P)
      have := congrArg (fun y : P => (y : J)) hxp
      simpa using this
    have hx3_ne : x ^ 3 ≠ 1 := by
      intro h
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h
      rw [hx9] at hdvd
      norm_num at hdvd
    exact hx3_ne hx3

theorem pRank_three_le_two_of_modelJ (J : Type) [Group J] [Finite J]
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup J) ≤ 2 := by
  apply CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) Nat.prime_three
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
  simpa using not_twentySeven_dvd_card_of_modelJ J hJ

theorem center_eq_bot_of_modelJ (J : Type) [Group J] [Finite J]
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) :
    Subgroup.center J = ⊥ := by
  rcases hJ with h4 | h5
  · have hsimple := isSimpleGroup_of_statedClassicalModel h4
    have hcard := card_of_statedClassicalModel_psl_four_two h4
    have hnotprime : ¬ (Nat.card J).Prime := by
      rw [hcard]
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 2 ∣ 20160) (by norm_num) (by norm_num)
    exact @center_eq_bot_of_simple_aux J _ _ hsimple hnotprime
  · have hsimple := isSimpleGroup_of_statedClassicalModel h5
    have hcard := card_of_statedClassicalModel_psl_five_two h5
    have hnotprime : ¬ (Nat.card J).Prime := by
      rw [hcard]
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 2 ∣ 9999360) (by norm_num) (by norm_num)
    exact @center_eq_bot_of_simple_aux J _ _ hsimple hnotprime

end CFSG.StandardType.FF81.CatQ1

end
