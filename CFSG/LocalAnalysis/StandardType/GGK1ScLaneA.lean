module

public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGK1ScLin
public import CFSG.LocalAnalysis.StandardType.GGK1ScUni

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggK1ScLane_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

private theorem ggK1ScLane_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
  have hge : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at *

theorem largeEvenLabelAll_centerPrime_clA
    {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGenericClA lab p) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨hgen, htag⟩ := hgen
  dsimp only at hgen htag hlab ⊢
  have hn1 : 1 ≤ n := hlab.1
  have hp : p.Prime := hgen.1
  have hp2 : p ≠ 2 := hgen.2.1
  intro Q hQ
  rcases htag with hA | htwA | ⟨hD, hr3⟩ | ⟨htwD, hrle3⟩
  · subst hA
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
    refine ⟨K, i1, i2, hK, hQR, ?_⟩
    letI := i1
    letI := i2
    haveI : CharP K 2 := charP_two_of_card hK
    have hpd : ¬ (p ∣ r + 1 ∧ p ∣ Nat.card K - 1) := by
      rw [hK]
      intro h
      exact hgen.2.2.2.2.1 ⟨rfl, h⟩
    exact ggCenterPrime_linear_gcd (d := r + 1) (by omega) hp hp2 hpd
  · subst htwA
    have hr2 : 2 ≤ r := hlab.2.1
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
    refine ⟨K, i1, i2, hK, hQR, ?_⟩
    letI := i1
    letI := i2
    have hdq : (r + 1, 2 ^ n) ≠ (3, 2) := by
      intro he
      have h1 : r + 1 = 3 := congrArg Prod.fst he
      have h2 : 2 ^ n = 2 := congrArg Prod.snd he
      have h3 : 2 ≤ n := hlab.2.2 (show r = 2 by omega)
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      omega
    have hpd : ¬ (p ∣ r + 1 ∧ p ∣ 2 ^ n + 1) := by
      intro h
      exact hgen.2.2.2.2.2 ⟨rfl, h⟩
    exact ggCenterPrime_unitary_gcd (d := r + 1) hK hn1 (by omega) hdq hp hp2 hpd
  · subst hD
    subst hr3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    dsimp only [LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
    refine ⟨K, i1, i2, hK, hQR, ?_⟩
    letI := i1
    letI := i2
    haveI : CharP K 2 := charP_two_of_card hK
    have hpd : ¬ (p ∣ 4 ∧ p ∣ Nat.card K - 1) :=
      fun h => ggK1ScLane_not_dvd_four hp hp2 h.1
    exact ggCenterPrime_linear_gcd (d := 4) (by norm_num) hp hp2 hpd
  · subst htwD
    have hr2 : 2 ≤ r := hlab.2
    interval_cases r
    · dsimp only [LargeEvenRawDatum] at hQ ⊢
      simp only [↓reduceIte] at hQ ⊢
      dsimp only [LargeEvenRecipeLinear] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
      refine ⟨K, i1, i2, hK, hQR, ?_⟩
      letI := i1
      letI := i2
      have hK' : Nat.card K = 2 ^ (2 * n) := by
        rw [hK, ← pow_mul, Nat.mul_comm]
      haveI : CharP K 2 := charP_two_of_card hK'
      have hpd : ¬ (p ∣ 2 ∧ p ∣ Nat.card K - 1) :=
        fun h => ggK1ScLane_not_dvd_two hp hp2 h.1
      exact ggCenterPrime_linear_gcd (d := 2) (by norm_num) hp hp2 hpd
    · dsimp only [LargeEvenRawDatum] at hQ ⊢
      simp only [↓reduceIte] at hQ ⊢
      dsimp only [LargeEvenRecipeUnitary] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
      refine ⟨K, i1, i2, hK, hQR, ?_⟩
      letI := i1
      letI := i2
      have hdq : (4, 2 ^ n) ≠ (3, 2) :=
        fun he => absurd (congrArg Prod.fst he) (by norm_num)
      have hpd : ¬ (p ∣ 4 ∧ p ∣ 2 ^ n + 1) :=
        fun h => ggK1ScLane_not_dvd_four hp hp2 h.1
      exact ggCenterPrime_unitary_gcd (d := 4) hK hn1 (by norm_num) hdq hp hp2 hpd

end CFSG.StandardType

end
