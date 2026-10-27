module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneNonMainB
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Centralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_sl28_center_eq_bot_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := CFSG.GroupTheory.isSimpleGroup_of_isSLn_two hm h
  haveI : Group.IsPerfect X := CFSG.GroupTheory.isPerfect_of_isSLn_two hm h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative X) inferInstance

theorem s16h_sl28_aut_seven_inner {X : Type} [Group X] [Finite X]
    (hX : IsSLn X 2 3) (α : MulAut X) (hα : α ^ 7 = 1) :
    ∃ x : X, α = MulAut.conj x := by
  have hL2 : UC22.IsL2 X 3 := CFSG.GroupTheory.isL2_of_isSLn_two (by norm_num) hX
  have hout : ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.not_seven_dvd_card_outer_of_isL2_three hL2
  have hdvd : orderOf α ∣ 7 := orderOf_dvd_of_pow_eq_one hα
  have hcop7 : Nat.Coprime 7
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :=
    Nat.prime_seven.coprime_iff_not_dvd.mpr hout
  have hcop : Nat.Coprime (orderOf α)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :=
    hcop7.coprime_dvd_left hdvd
  have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
    CFSG.OddStandard.AltStdSec.SwapPartner.mem_inner_of_coprime_orderOf_outer hcop
  obtain ⟨x, hx⟩ := hin
  exact ⟨x, hx.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
