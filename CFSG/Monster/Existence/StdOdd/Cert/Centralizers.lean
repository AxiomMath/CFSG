module

public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.LieType.Chevalley.C2E6Std

private theorem card_rgrp :
    Nat.card Rgrp = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
  rw [card_stdGroup]
  norm_num

theorem centralizerFacts_of_reps
    (h5 : Nat.card (Subgroup.centralizer ({rep5} : Set Rgrp)) = 100800)
    (h7A : Nat.card (Subgroup.centralizer ({rep7A} : Set Rgrp)) = 141120)
    (h7B : Nat.card (Subgroup.centralizer ({rep7B} : Set Rgrp)) = 1176)
    (h11 : Nat.card (Subgroup.centralizer ({rep11} : Set Rgrp)) = 66)
    (h13 : Nat.card (Subgroup.centralizer ({rep13} : Set Rgrp)) = 13)
    (h17 : Nat.card (Subgroup.centralizer ({rep17} : Set Rgrp)) = 17)
    (h19 : Nat.card (Subgroup.centralizer ({rep19} : Set Rgrp)) = 19) :
    CentralizerFacts Rgrp := by
  have : Finite Rgrp := rgrp_finite
  have f5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have f7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have f11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have f13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have f17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have f19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨y₀, hy₀, hc, hind, hconj⟩ := sylow_five_fusion
    refine card_centralizer_dvd_of_sylow_elementary (p := 5) (reps := {rep5}) ?_ orderOf_rep5 hy₀ hc
      hind ⟨rep5, rfl, IsConj.refl _⟩ (fun i hi => ⟨rep5, rfl, hconj i hi⟩) ?_
    · rw [card_rgrp]
      norm_num
    · intro r hr
      rw [Set.mem_singleton_iff.1 hr, h5]
      norm_num
  ·
    obtain ⟨x₀, y₀, hx₀, hy₀, hc, hind, h0, hi⟩ := sylow_seven_fusion
    refine card_centralizer_dvd_of_sylow_elementary (p := 7) (reps := {rep7A, rep7B}) ?_ hx₀ hy₀ hc
      hind ?_ (fun i hi' => ?_) ?_
    · rw [card_rgrp]
      norm_num
    · rcases h0 with h | h
      · exact ⟨rep7A, by simp, h⟩
      · exact ⟨rep7B, by simp, h⟩
    · rcases hi i hi' with h | h
      · exact ⟨rep7A, by simp, h⟩
      · exact ⟨rep7B, by simp, h⟩
    · intro r hr
      rcases hr with rfl | hr
      · rw [h7A]
        norm_num
      · rw [Set.mem_singleton_iff.1 hr, h7B]
        norm_num
  ·
    intro x hx
    have hp2 : ¬ 11 ^ 2 ∣ Nat.card Rgrp := by
      rw [card_rgrp]
      norm_num
    rw [card_centralizer_eq_of_sylow_prime hp2 orderOf_rep11 hx, h11]
  ·
    intro x hx
    have hp2 : ¬ 13 ^ 2 ∣ Nat.card Rgrp := by
      rw [card_rgrp]
      norm_num
    rw [card_centralizer_eq_of_sylow_prime hp2 orderOf_rep13 hx, h13]
  ·
    intro x hx
    have hp2 : ¬ 17 ^ 2 ∣ Nat.card Rgrp := by
      rw [card_rgrp]
      norm_num
    rw [card_centralizer_eq_of_sylow_prime hp2 orderOf_rep17 hx, h17]
    norm_num
  ·
    intro x hx
    have hp2 : ¬ 19 ^ 2 ∣ Nat.card Rgrp := by
      rw [card_rgrp]
      norm_num
    rw [card_centralizer_eq_of_sylow_prime hp2 orderOf_rep19 hx, h19]
    norm_num

end CFSG.Monster.Existence.StdOdd.Cert
