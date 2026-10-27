module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private def s16t3_M : ℕ := 2 ^ 21 * 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127

private theorem s16t3_prime_dvd_of_dvd_M {p : ℕ} (hp : p.Prime) (h : p ∣ s16t3_M) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 ∨ p = 127 := by
  have hM : s16t3_M = 2 ^ 21 * (3 ^ 4 * (5 * (7 ^ 2 * (31 * 127)))) := by
    simp [s16t3_M]
  rw [hM] at h
  rw [hp.dvd_mul] at h
  rcases h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · rw [hp.dvd_mul] at h
    rcases h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp
        (hp.dvd_of_dvd_pow h)))
    · rw [hp.dvd_mul] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h)))
      · rw [hp.dvd_mul] at h
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp
              (hp.dvd_of_dvd_pow h)))))
        · rw [hp.dvd_mul] at h
          rcases h with h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)).mp h)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)).mp h)))))

private theorem s16t3_not_pow_three_dvd (N : ℕ) (hN : N ∣ s16t3_M) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ N := by
  intro p hp h5 hdiv
  have hpM : p ∣ s16t3_M :=
    dvd_trans (dvd_trans (dvd_pow_self p (by norm_num)) hdiv) hN
  rcases s16t3_prime_dvd_of_dvd_M hp hpM with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact absurd (dvd_trans hdiv hN) (by norm_num [s16t3_M])
  · exact absurd (dvd_trans hdiv hN) (by norm_num [s16t3_M])
  · exact absurd (dvd_trans hdiv hN) (by norm_num [s16t3_M])
  · exact absurd (dvd_trans hdiv hN) (by norm_num [s16t3_M])

private theorem s16t3_card_statedSL_zero {K : Type} [Field K] [Finite K] :
    Nat.card (StatedSL 0 K) = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hGL : Nat.card (GL (Fin 0) K) = 1 := by
    rw [Matrix.card_GL_field]
    simp
  have hdvd : Nat.card (StatedSL 0 K) ∣ Nat.card (GL (Fin 0) K) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hGL] at hdvd
  exact Nat.dvd_one.mp hdvd

private theorem s16t3_card_statedSL_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card (StatedSL 1 K) = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, Fin.prod_univ_one,
    ← Nat.card_eq_fintype_card, hK]
  norm_num

private theorem s16t3_card_statedSL_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card (StatedSL 2 K) = 6 := by
  rw [CFSG.Open.StatedAPI.card_statedSL_two K, hK]
  norm_num

private theorem s16t3_card_statedSL_six {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card (StatedSL 6 K) = 20158709760 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, Fin.prod_univ_six,
    ← Nat.card_eq_fintype_card, hK]
  rfl

private theorem s16t3_card_statedSL_seven {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card (StatedSL 7 K) = 163849992929280 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, Fin.prod_univ_seven,
    ← Nat.card_eq_fintype_card, hK]
  rfl

theorem s16t3_val_card_sl {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    {n : ℕ} (hX : IsSLn X n 1) (hn : n < 8) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ Nat.card X) ∧
      (7 ^ 2 ∣ Nat.card X → IsSLn X 6 1 ∨ IsSLn X 7 1) := by
  have hXmem : IsSLn X n 1 := hX
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hX
  letI := hKf
  letI := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hcard : Nat.card X = Nat.card (StatedSL n K) := Nat.card_congr e.toEquiv
  have hn8 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases hn8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hcard, s16t3_card_statedSL_zero]
    exact ⟨s16t3_not_pow_three_dvd 1 (by norm_num [s16t3_M]),
      fun h => by norm_num at h⟩
  · rw [hcard, s16t3_card_statedSL_one hK2]
    exact ⟨s16t3_not_pow_three_dvd 1 (by norm_num [s16t3_M]),
      fun h => by norm_num at h⟩
  · rw [hcard, s16t3_card_statedSL_two hK2]
    exact ⟨s16t3_not_pow_three_dvd 6 (by norm_num [s16t3_M]),
      fun h => by norm_num at h⟩
  · rw [hcard, CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hK2]
    exact ⟨s16t3_not_pow_three_dvd 168 (by norm_num [s16t3_M]),
      fun h => by norm_num at h⟩
  · rw [hcard, CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK2]
    exact ⟨s16t3_not_pow_three_dvd 20160 (by norm_num [s16t3_M]),
      fun h => by norm_num at h⟩
  · rw [hcard, CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK2]
    exact ⟨s16t3_not_pow_three_dvd 9999360 (by norm_num [s16t3_M]),
      fun h => by norm_num at h⟩
  · rw [hcard, s16t3_card_statedSL_six hK2]
    exact ⟨s16t3_not_pow_three_dvd 20158709760 (by norm_num [s16t3_M]),
      fun _ => Or.inl hXmem⟩
  · rw [hcard, s16t3_card_statedSL_seven hK2]
    exact ⟨s16t3_not_pow_three_dvd 163849992929280 (by norm_num [s16t3_M]),
      fun _ => Or.inr hXmem⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
