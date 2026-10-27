module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [Group X] [Finite X]

theorem pRank_top_le_one_of_s15ListTwo
    {X : Type} [Group X] [Finite X]
    (h : s15ListTwo X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  by_contra hle
  have h2 : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by omega
  have hle_fact := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
    (A := X) hq
  have hfact : 2 ≤ (Nat.card X).factorization q := h2.trans hle_fact
  have hdvd : q ^ 2 ∣ Nat.card X :=
    (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr hfact
  rcases h with hL3 | hAlt5
  · obtain ⟨hcard, -⟩ := s15k_six_l3 hL3
    rw [hcard] at hdvd
    have hq_not2 : ¬ q ∣ 2 ^ 3 := by
      intro h
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2')
    by_cases hq168 : q ∣ 168
    · have h168_eq : 168 = 2 ^ 3 * 3 * 7 := by norm_num
      rw [h168_eq] at hq168
      have hq37 : q ∣ 3 * 7 := by
        have h := hq.dvd_mul.mp hq168
        rcases h with h2 | h37
        · have h23 := hq.dvd_mul.mp h2
          rcases h23 with h2' | h3
          · exact absurd h2' hq_not2
          · exact h3.trans (dvd_mul_right 3 7)
        · exact h37.trans (dvd_mul_left 7 3)
      have hq3_or_7 : q = 3 ∨ q = 7 := by
        have h := hq.dvd_mul.mp hq37
        rcases h with h3 | h7
        · left
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
        · right
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp h7
      rcases hq3_or_7 with rfl | rfl
      · norm_num at hdvd
      · norm_num at hdvd
    · have hq_dvd_q2 : q ∣ q ^ 2 := by
        rw [pow_two]
        exact dvd_mul_right q q
      exact hq168 (hq_dvd_q2.trans hdvd)
  · have hcard := s15k_six_alt_card hAlt5 (by norm_num)
    have hcard' : Nat.card X = 60 := by
      rw [hcard]
      norm_num
    rw [hcard'] at hdvd
    have hq_not2 : ¬ q ∣ 2 ^ 2 := by
      intro h
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2')
    by_cases hq60 : q ∣ 60
    · have h60_eq : 60 = 2 ^ 2 * 3 * 5 := by norm_num
      rw [h60_eq] at hq60
      have hq35 : q ∣ 3 * 5 := by
        have h := hq.dvd_mul.mp hq60
        rcases h with h2 | h35
        · have h23 := hq.dvd_mul.mp h2
          rcases h23 with h2' | h3
          · exact absurd h2' hq_not2
          · exact h3.trans (dvd_mul_right 3 5)
        · exact h35.trans (dvd_mul_left 5 3)
      have hq3_or_5 : q = 3 ∨ q = 5 := by
        have h := hq.dvd_mul.mp hq35
        rcases h with h3 | h5
        · left
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
        · right
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5
      rcases hq3_or_5 with rfl | rfl
      · norm_num at hdvd
      · norm_num at hdvd
    · have hq_dvd_q2 : q ∣ q ^ 2 := by
        rw [pow_two]
        exact dvd_mul_right q q
      exact hq60 (hq_dvd_q2.trans hdvd)

theorem not_s15ListTwo_of_odd_pRank
    {W : Type} [Group W] [Finite W] {H : Subgroup W}
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q H) :
    ¬ s15ListTwo ↥H := by
  obtain ⟨q, hq, hq2, hrank⟩ := hodd
  intro hlist
  have h1 : CFSG.Open.pRank q (⊤ : Subgroup ↥H) ≤ 1 :=
    pRank_top_le_one_of_s15ListTwo hlist hq hq2
  have h2 : CFSG.Open.pRank q H = CFSG.Open.pRank q (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
  rw [h2] at hrank
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
