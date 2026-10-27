module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem s16t3_center_bot_of_simple {X : Type} [Group X] (hS : IsSimpleGroup X)
    (hnp : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  haveI := hS
  apply TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
  intro hc
  haveI := hc
  exact hnp (Group.is_simple_iff_prime_card.mp hS)

private theorem s16t3_conj_injective {S : Type} [Group S] (hz : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxc : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * x = (x * g * x⁻¹) * x := by rw [h1]
      _ = x * g := by group
  rw [hz, Subgroup.mem_bot] at hxc
  exact hxc

private theorem s16t3_card_inner {S : Type} [Group S] (hz : Subgroup.center S = ⊥) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) = Nat.card S := by
  unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
  exact (Nat.card_congr (MonoidHom.ofInjective (s16t3_conj_injective hz)).toEquiv).symm

private theorem s16t3_card_outer_dvd_of_mulAut_dvd {S : Type} [Group S] [Finite S] {k : ℕ}
    (hz : Subgroup.center S = ⊥) (hdvd : Nat.card (MulAut S) ∣ k * Nat.card S) :
    Nat.card (Outer S) ∣ k := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  rw [s16t3_card_inner hz] at hcard
  rw [hcard] at hdvd
  haveI : Nonempty S := ⟨1⟩
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd

private theorem s16t3_not_three_dvd_of_dvd {S : Type} [Group S] {k : ℕ}
    (hdvd : Nat.card (Outer S) ∣ k) (hk : ¬ 3 ∣ k) : ¬ 3 ∣ Nat.card (Outer S) :=
  fun h => hk (h.trans hdvd)

private theorem s16t3_sp_not_three_dvd {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hsp : IsSpn X n 1) (hn : n < 8) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hq hsp
  obtain ⟨k, hk⟩ := hsp.1
  have hne : n = 6 := by omega
  rw [hne] at hsp
  have hz : Subgroup.center X = ⊥ :=
    s16t3_center_bot_of_simple (s16c167_cfg2_simple_sp hsp)
      (by rw [s16c1610_card_of_isSpn_six hsp]; norm_num)
  have hdvd : Nat.card (MulAut X) ∣ Nat.card X := s16e_two_sp_card_aut_dvd hsp
  refine s16t3_not_three_dvd_of_dvd (k := 1)
    (s16t3_card_outer_dvd_of_mulAut_dvd (k := 1) hz ?_) (by norm_num)
  simpa only [one_mul] using hdvd

private theorem s16t3_alt_not_three_dvd {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hA : IsAlt X n) (hn : n < 12) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hq hA
  by_cases hn6 : n = 6
  · rw [hn6] at hA
    have hz : Subgroup.center X = ⊥ :=
      s16t3_center_bot_of_simple (s16c167_cfg2_simple_alt (by norm_num) hA)
        (by rw [s15k_six_alt_card hA (by norm_num)]; norm_num [Nat.factorial])
    have hcard : Nat.card X = 360 := by
      rw [s15k_six_alt_card hA (by norm_num)]; norm_num [Nat.factorial]
    have hdvd : Nat.card (MulAut X) ∣ 4 * Nat.card X := by
      have h := s16e_two_alt6_card_aut_dvd hA
      rw [← hcard] at h
      exact h
    exact s16t3_not_three_dvd_of_dvd (k := 4)
      (s16t3_card_outer_dvd_of_mulAut_dvd (k := 4) hz hdvd) (by norm_num)
  · have hz : Subgroup.center X = ⊥ := s16c1610_center_of_isAlt (by omega) hA
    have hn' : n = 5 ∨ 7 ≤ n := by omega
    have hbound : Nat.card (MulAut X) ≤ 2 * Nat.card X := (s15k_six_alt hA hn').2
    have hdvd : Nat.card (MulAut X) ∣ 2 * Nat.card X :=
      s16e_two_card_aut_dvd_of_le hz hbound
    exact s16t3_not_three_dvd_of_dvd (k := 2)
      (s16t3_card_outer_dvd_of_mulAut_dvd (k := 2) hz hdvd) (by norm_num)

private theorem s16t3_omegaPlus_not_three_dvd {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hOP : IsOmegaPlus X n 1) (hn : n < 8) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hq hOP
  obtain ⟨k, hk⟩ := hOP.1
  have hne : n = 6 := by omega
  rw [hne] at hOP
  exact s16t3_alt_not_three_dvd hq (s15k_omp6_isAlt8 hOP) (by norm_num)

private theorem s16t3_omegaMinus_not_three_dvd {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hOM : IsOmegaMinus X n 1) (hn : n < 10) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hq hOM
  obtain ⟨k, hk⟩ := hOM.1
  have hn' : n = 4 ∨ n = 6 ∨ n = 8 := by omega
  rcases hn' with h4 | h6 | h8
  · rw [h4] at hOM
    exact s16t3_alt_not_three_dvd hq (s16k_isAlt_five_of_isOmegaMinus_four hOM) (by norm_num)
  · rw [h6] at hOM
    have hz : Subgroup.center X = ⊥ :=
      s16t3_center_bot_of_simple (s16c1_isSimpleGroup_of_isOmegaMinus_six hOM)
        (by rw [(s15k_six_om6 hOM).1]; norm_num)
    have hdvd : Nat.card (MulAut X) ∣ 2 * Nat.card X :=
      s16e_two_om_card_aut_dvd (Or.inl rfl) hOM
    exact s16t3_not_three_dvd_of_dvd (k := 2)
      (s16t3_card_outer_dvd_of_mulAut_dvd (k := 2) hz hdvd) (by norm_num)
  · rw [h8] at hOM
    exact s16t3_not_three_dvd_of_dvd (s16e_two_om_card_outer_eight hOM) (by norm_num)

theorem s16t3_not_three_dvd_outer_a {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X)
    (hX : ∃ n : ℕ, (IsSpn X n 1 ∧ n < 8) ∨ (IsOmegaPlus X n 1 ∧ n < 8) ∨
      (IsOmegaMinus X n 1 ∧ n < 10) ∨ (UC22.IsAlt X n ∧ n < 12)) :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  obtain ⟨n, h | h | h | h⟩ := hX
  · exact s16t3_sp_not_three_dvd hq h.1 h.2
  · exact s16t3_omegaPlus_not_three_dvd hq h.1 h.2
  · exact s16t3_omegaMinus_not_three_dvd hq h.1 h.2
  · exact s16t3_alt_not_three_dvd hq h.1 h.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
