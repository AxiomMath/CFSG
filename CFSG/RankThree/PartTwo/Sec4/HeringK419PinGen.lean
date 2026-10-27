module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinNum

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.RankThree.PartTwo.Sec11.KSListsProof

theorem contra_pow {P M : ℕ} (hP : 1 ≤ P) (h1 : M ^ 2 < P ^ 5) (h2 : P ^ 8 ≤ M ^ 3) : False := by
  have h3 : (M ^ 2) ^ 3 < (P ^ 5) ^ 3 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h4 : (P ^ 8) ^ 2 ≤ (M ^ 3) ^ 2 := Nat.pow_le_pow_left h2 2
  have h5 : P ^ 15 ≤ P ^ 16 := Nat.pow_le_pow_right hP (by norm_num)
  have : P ^ 16 < P ^ 16 :=
    calc P ^ 16 = (P ^ 8) ^ 2 := by ring
      _ ≤ (M ^ 3) ^ 2 := h4
      _ = (M ^ 2) ^ 3 := by ring
      _ < (P ^ 5) ^ 3 := h3
      _ = P ^ 15 := by ring
      _ ≤ P ^ 16 := h5
  exact lt_irrefl _ this

theorem size_contra {M P B L d dmax : ℕ} (hdm : 0 < dmax) (h1 : M ^ 2 < P ^ 5) (h2 : P ≤ B)
    (h3 : L ≤ M * d) (h4 : d ≤ dmax) (h5 : B ^ 5 * dmax ^ 2 ≤ L ^ 2) : False := by
  have a : P ^ 5 ≤ B ^ 5 := Nat.pow_le_pow_left h2 5
  have b : L ^ 2 ≤ (M * d) ^ 2 := Nat.pow_le_pow_left h3 2
  have c : (M * d) ^ 2 ≤ (M * dmax) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left M h4) 2
  have hd2 : 0 < dmax ^ 2 := by positivity
  have : M ^ 2 * dmax ^ 2 < M ^ 2 * dmax ^ 2 :=
    calc M ^ 2 * dmax ^ 2 < P ^ 5 * dmax ^ 2 := Nat.mul_lt_mul_of_pos_right h1 hd2
      _ ≤ B ^ 5 * dmax ^ 2 := Nat.mul_le_mul_right _ a
      _ ≤ L ^ 2 := h5
      _ ≤ (M * d) ^ 2 := b
      _ ≤ (M * dmax) ^ 2 := c
      _ = M ^ 2 * dmax ^ 2 := by ring
  exact lt_irrefl _ this

theorem padicValNat_eq_of_exact {p k M : ℕ} (hp : p.Prime) (h1 : p ^ k ∣ M)
    (h2 : ¬ p ^ (k + 1) ∣ M) : padicValNat p M = k := by
  haveI := Fact.mk hp
  have hM0 : M ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have a := (padicValNat_dvd_iff_le hM0).mp h1
  have b : ¬ k + 1 ≤ padicValNat p M := fun h => h2 ((padicValNat_dvd_iff_le hM0).mpr h)
  omega

theorem two_adic_contra {M Q f N : ℕ} (hQ : Q = 2 ^ f) (hM0 : M ≠ 0)
    (h : 2 ^ (8 * padicValNat 2 M) ≤ M ^ 3) (hd : 2 ^ (f * N) ∣ M)
    (hM : M ^ 3 < Q ^ (8 * N)) : False := by
  have h1 : f * N ≤ padicValNat 2 M := (padicValNat_dvd_iff_le hM0).mp hd
  have h2 : 2 ^ (8 * (f * N)) ≤ 2 ^ (8 * padicValNat 2 M) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : Q ^ (8 * N) = 2 ^ (8 * (f * N)) := by rw [hQ, ← pow_mul]; ring_nf
  omega

theorem k_eq_of_exact {p k m M : ℕ} (h1 : p ^ k ∣ M) (h2 : ¬ p ^ (k + 1) ∣ M)
    (h3 : p ^ m ∣ M) (h4 : ¬ p ^ (m + 1) ∣ M) : k = m := by
  have a : k ≤ m := by
    by_contra h
    push Not at h
    exact h4 ((pow_dvd_pow p h).trans h1)
  have b : m ≤ k := by
    by_contra h
    push Not at h
    exact h2 ((pow_dvd_pow p h).trans h3)
  omega

theorem caseII_small {M p e m d C : ℕ} (hX : XInfo M p e) (hd : ¬ p ∣ d) (hC : ¬ p ∣ C)
    (h : M * d = p ^ m * C) (hm : m < 8) : False := by
  obtain ⟨k, hk8, hdvd, hndvd, -⟩ := hX.ex
  have h1 := exact_pow_of_mul_eq hX.prime hd hC h
  have := k_eq_of_exact hdvd hndvd h1.1 h1.2
  omega

theorem char2_engine {M N N' w w' : ℕ} {Z : ℕ → Prop} (hX : Profile M N Z)
    (hXle : ∀ k, Z k → k ≤ w) (hw6 : 6 ≤ w) (hwN : w < N)
    (hY2 : ∃ r, Odd r ∧ M = 2 ^ N' * r) (hNw : N' ≤ w') (hw'2 : 2 ≤ w')
    (hYp : ∀ q, IsPrimitivePrimeDivisor q w' → q ∣ M) : False := by
  obtain ⟨r, hr, hMr⟩ := hY2
  obtain ⟨s, hs, hMs⟩ := hX.two
  have hN : N = N' := eq_of_two_pow_mul_odd hs hr (hMs.symm.trans hMr)
  have hw'w : w' ≤ w := by
    by_cases h6 : w' = 6
    · omega
    · obtain ⟨q, hq⟩ := exists_isPrimitivePrimeDivisor hw'2 h6
      exact hXle w' ((hX.prim q w' hq (by omega)).mp (hYp q hq))
  omega

theorem mul_sq_sub_one' {x : ℕ} (hx : 1 ≤ x) : x * (x ^ 2 - 1) = (x - 1) * x * (x + 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hx, h2]
  ring

theorem pow_le_of_dvd_psl2' {p k x m d : ℕ} (hp : p.Prime) (hx : 3 ≤ x)
    (hd : (Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) (hdvd : p ^ k ∣ m)
    (h : m * d = x * (x ^ 2 - 1)) : p ^ k ≤ x + 1 := by
  rw [mul_sq_sub_one' (by omega)] at h
  by_cases hp2 : p = 2
  · subst hp2
    rcases hd with ⟨hxo, rfl⟩ | ⟨hxe, rfl⟩
    · have h2 : 2 ^ (k + 1) ∣ (x - 1) * (x + 1) := by
        have h1 : 2 ^ (k + 1) ∣ x * ((x - 1) * (x + 1)) := by
          rw [pow_succ, show x * ((x - 1) * (x + 1)) = (x - 1) * x * (x + 1) by ring, ← h]
          exact Nat.mul_dvd_mul_right hdvd 2
        exact (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxo)).dvd_of_dvd_mul_left h1
      exact two_pow_le_of_dvd_mul_succ hxo (by omega) h2
    · rw [mul_one] at h
      exact pow_le_succ_of_dvd_consecutive Nat.prime_two
        (Or.inr (even_iff_two_dvd.mp hxe)) (by omega) (h ▸ hdvd)
  · exact pow_le_succ_of_dvd_consecutive hp (Or.inl hp2) (by omega)
      (h ▸ Dvd.dvd.mul_right hdvd d)

theorem psl2_ineq {x : ℕ} (hx : 9 ≤ x) : (x + 1) ^ 5 * 2 ^ 2 ≤ (x * (x ^ 2 - 1)) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 9 := ⟨x - 9, by omega⟩
  have h1 : 1 ≤ (t + 9) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  have : (0 : ℤ) ≤ (((t : ℤ) + 9) * (((t : ℤ) + 9) ^ 2 - 1)) ^ 2 -
      ((t : ℤ) + 9 + 1) ^ 5 * 2 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem not_psl2 {M p e x d : ℕ} (hX : XInfo M p e) (hx : 2 ≤ x)
    (hd : (Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) (h : M * d = x * (x ^ 2 - 1)) : False := by
  obtain ⟨k, hk8, hdvd, hndvd, hsize⟩ := hX.ex
  have hP : 2 ^ 8 ≤ p ^ k :=
    (Nat.pow_le_pow_right (by norm_num) hk8).trans (Nat.pow_le_pow_left hX.prime.two_le k)
  have hM0 : M ≠ 0 := by rintro rfl; exact hndvd (dvd_zero _)
  have hd1 : 1 ≤ d := by rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hMP : 2 ^ 8 ≤ M := hP.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hdvd)
  have hx4 : 4 ≤ x := by
    by_contra hc
    push Not at hc
    have hMd : M ≤ M * d := Nat.le_mul_of_pos_right M hd1
    interval_cases x <;> omega
  have hle := pow_le_of_dvd_psl2' hX.prime (by omega) hd hdvd h
  have hx9 : 9 ≤ x := by norm_num at hP; omega
  have hd2 : d ≤ 2 := by rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  exact size_contra (by norm_num) hsize hle (le_of_eq h.symm) hd2 (psl2_ineq hx9)

end CFSG.RankThree.PartTwo.Sec4.HeringPin
