module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s15k_aut_pRank_of_card {S H : Type} [Group S] [Group H] [Finite S] [Finite H]
    (f : S →* H) (hf : Function.Injective f) (hn : f.range.Normal) {k : ℕ}
    (hk : f.range.index = 2 ^ k) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r : ℕ)
    (hN : ¬ p ^ (r + 1) ∣ Nat.card S) : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ r := by
  refine s15k_out_pRank_le f hf hn hk (hp.odd_of_ne_two hp2) r ?_
  intro E _ j hj
  by_contra hjr
  refine hN ?_
  have h1 : p ^ (r + 1) ∣ p ^ j := pow_dvd_pow p (not_le.mp hjr)
  rw [← hj] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card E)

private theorem s15k_aut_sq {N : ℕ} (hN : N ≠ 0) (T : Finset ℕ)
    (hT : ∀ q ∈ N.primeFactors, q ∉ T → ¬ q ^ 2 ∣ N) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) :
    ¬ p ^ 2 ∣ N := fun h =>
  hT p (Nat.mem_primeFactors.mpr ⟨hp, dvd_trans (dvd_pow_self p two_ne_zero) h, hN⟩) hpT h

private theorem s15k_aut_dvd {N k p : ℕ} (hp : p.Prime) (hN : N ≠ 0) (hd : p ∣ N * 2 ^ k) :
    p = 2 ∨ p ∈ N.primeFactors := by
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact Or.inr (Nat.mem_primeFactors.mpr ⟨hp, h, hN⟩)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

private theorem s15k_aut_card_two {S : Type} [Group S] (hS : s15ListTwo S) :
    Nat.card S = 168 ∨ Nat.card S = 60 := by
  rcases hS with h | h
  · exact Or.inl (s15k_six_l3 h).1
  · refine Or.inr ?_
    rw [s15k_six_alt_card h (by norm_num)]
    norm_num [Nat.factorial]

private theorem s15k_aut_card_four {S : Type} [Group S] (hS : s15ListFour S) :
    Nat.card S = 25920 ∨ Nat.card S = 360 ∨ Nat.card S = 2520 ∨ Nat.card S = 20160 := by
  rcases hS with h | h | h | h
  · exact Or.inl (s15k_six_om6 h).1
  · refine Or.inr (Or.inl ?_)
    rw [s15k_six_alt_card h (by norm_num)]
    norm_num [Nat.factorial]
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [s15k_six_alt_card h (by norm_num)]
    norm_num [Nat.factorial]
  · exact Or.inr (Or.inr (Or.inr (s15k_six_l4 h).1))

theorem rAutRank153_holds : RAutRank153 := by
  intro S H _ _ _ _ f hf hn hc
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · obtain ⟨k, hk⟩ := s15k_six_index_pow f hf hn hc ((s15ExcList_iff S).mpr (Or.inl hS))
    have hcard : Nat.card H = Nat.card S * 2 ^ k := by
      rw [← s15k_out_card_eq f hf, hk]
    refine ⟨fun p hp hp2 => ?_, fun hL p hp hpd => ?_, fun hA p hp hpd => ?_⟩
    · refine s15k_aut_pRank_of_card f hf hn hk hp hp2 1 ?_
      rcases s15k_aut_card_two hS with hN | hN
      · rw [hN]
        exact s15k_aut_sq (by norm_num) {2} (by simp [Nat.primeFactors]) hp (by simpa using hp2)
      · rw [hN]
        exact s15k_aut_sq (by norm_num) {2} (by simp [Nat.primeFactors]) hp (by simpa using hp2)
    · rw [hcard, (s15k_six_l3 hL).1] at hpd
      rcases s15k_aut_dvd hp (by norm_num) hpd with h | h
      · exact Or.inl h
      · have h168 : Nat.primeFactors 168 = {2, 3, 7} := by simp [Nat.primeFactors]
        rw [h168] at h
        simpa using h
    · rw [hcard, s15k_six_alt_card hA (by norm_num)] at hpd
      have h60 : Nat.factorial 5 / 2 = 60 := by norm_num [Nat.factorial]
      rw [h60] at hpd
      rcases s15k_aut_dvd hp (by norm_num) hpd with h | h
      · exact Or.inl h
      · have h60 : Nat.primeFactors 60 = {2, 3, 5} := by simp [Nat.primeFactors]
        rw [h60] at h
        simpa using h
  · obtain ⟨k, hk⟩ := s15k_six_index_pow f hf hn hc ((s15ExcList_iff S).mpr (Or.inr hS))
    have h3 : ¬ IsOmegaMinus S 6 1 → CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2 := by
      intro hO
      refine s15k_aut_pRank_of_card f hf hn hk Nat.prime_three (by norm_num) 2 ?_
      rcases hS with h | h | h | h
      · exact absurd h hO
      · rw [s15k_six_alt_card h (by norm_num)]
        norm_num [Nat.factorial]
      · rw [s15k_six_alt_card h (by norm_num)]
        norm_num [Nat.factorial]
      · rw [(s15k_six_l4 h).1]
        norm_num
    refine ⟨fun p hp hp2 hp3 => ?_, ?_, h3⟩
    · refine s15k_aut_pRank_of_card f hf hn hk hp hp2 1 ?_
      rcases s15k_aut_card_four hS with hN | hN | hN | hN <;> rw [hN] <;>
        exact s15k_aut_sq (by norm_num) {2, 3} (by simp [Nat.primeFactors]) hp
          (by simp [hp2, hp3])
    · by_cases hO : IsOmegaMinus S 6 1
      · refine s15k_out_pRank_le f hf hn hk (p := 3) (by decide) 3 ?_
        intro E hE j hj
        have h27 := s15k_om6_card_le hO E hE
        rw [hj] at h27
        by_contra hjr
        have h4 : 3 ^ 4 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (not_le.mp hjr)
        omega
      · exact (h3 hO).trans (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
