module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinGen

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.RankThree.PartTwo.Sec11.KSListsProof

theorem family_core {M p e s g d C N dmax B : ℕ} (hX : XInfo M p e) (hs : s.Prime) (hg : 1 ≤ g)
    (hMC : M * d = (s ^ g) ^ N * C) (hd : d ≤ dmax) (hdm : 0 < dmax)
    (hCs : ¬ s ∣ C) (hds : ¬ s ∣ d)
    (hN : s ≠ 2 → g * N < 8)
    (hpow : s ≠ 2 → ∀ r k : ℕ, r.Prime → r ≠ 2 → r ^ k ∣ C → r ^ k ≤ B)
    (hineq : s ≠ 2 → 3 ^ 8 ≤ B → B ^ 5 * dmax ^ 2 ≤ ((s ^ g) ^ N * C) ^ 2)
    (hK : s ≠ 2 → p = 2 → 2 ^ (8 * padicValNat 2 M) ≤ M ^ 3)
    (hlt : s = 2 → M ^ 3 < (2 ^ g) ^ (8 * N))
    (hppd : s = 2 → ∃ w, g * N ≤ w ∧ 2 ≤ w ∧
      ∀ q, IsPrimitivePrimeDivisor q w → q ∣ C ∧ ¬ q ∣ d) : False := by
  obtain ⟨k, hk8, hdvd, hndvd, hsize⟩ := hX.ex
  have hp := hX.prime
  have hM0 : M ≠ 0 := by rintro rfl; exact hndvd (dvd_zero _)
  by_cases hps : p = s
  · subst hps
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨Z, N', w, hprof, hle, hw6, hwN⟩ := hX.prof rfl
      obtain ⟨w', hNw, hw2, hq⟩ := hppd rfl
      have hcop : Nat.Coprime (2 ^ (g * N)) d :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hds)
      have h2 : 2 ^ (g * N) ∣ M :=
        hcop.dvd_of_dvd_mul_right (by rw [hMC, ← pow_mul]; exact Dvd.intro _ rfl)
      obtain ⟨r, hr⟩ := h2
      have hrd : r * d = C := by
        have h1 := hMC
        rw [hr, ← pow_mul] at h1
        exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) (by rw [← mul_assoc]; exact h1)
      refine char2_engine hprof hle hw6 hwN ⟨r, ?_, hr⟩ hNw hw2 fun q hq' => ?_
      · exact Nat.not_even_iff_odd.mp fun hev =>
          hCs (hrd ▸ Dvd.dvd.mul_right (even_iff_two_dvd.mp hev) d)
      · obtain ⟨hqC, hqd⟩ := hq q hq'
        have hqMd : q ∣ M * d := by rw [hMC]; exact Dvd.dvd.mul_left hqC _
        exact ((Nat.Prime.dvd_mul hq'.prime).mp hqMd).resolve_right hqd
    · exact caseII_small hX hds hCs (by rw [hMC, ← pow_mul]) (hN hp2)
  · by_cases hp2 : p = 2
    · subst hp2
      have hs2 : s ≠ 2 := fun h => hps h.symm
      have hv := padicValNat_eq_of_exact hp hdvd hndvd
      have hK' := hK hs2 rfl
      rw [hv] at hK'
      exact contra_pow (Nat.one_le_two_pow) hsize (by rw [← pow_mul, mul_comm]; exact hK')
    · by_cases hs2 : s = 2
      · subst hs2
        have hK' := hX.two hp2
        have hcop : Nat.Coprime (2 ^ (g * N)) d :=
          Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hds)
        have h2 : 2 ^ (g * N) ∣ M :=
          hcop.dvd_of_dvd_mul_right (by rw [hMC, ← pow_mul]; exact Dvd.intro _ rfl)
        exact two_adic_contra rfl hM0 hK' h2 (hlt rfl)
      · have hcop : Nat.Coprime (p ^ k) ((s ^ g) ^ N) := by
          rw [← pow_mul]
          exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hs).mpr hps)
        have hpC : p ^ k ∣ C :=
          hcop.dvd_of_dvd_mul_left (by rw [← hMC]; exact Dvd.dvd.mul_right hdvd d)
        have hle := hpow hs2 p k hp hp2 hpC
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hP3 : 3 ^ 8 ≤ p ^ k :=
          (Nat.pow_le_pow_right (by norm_num) hk8).trans (Nat.pow_le_pow_left hp3 k)
        exact size_contra hdm hsize hle (le_of_eq hMC.symm) hd (hineq hs2 (hP3.trans hle))

theorem cube_lt_of_lt_pow {M d Q D N : ℕ} (hd : 1 ≤ d) (h : M * d < Q ^ D) (hQ : 2 ≤ Q)
    (hDN : 3 * D ≤ 8 * N) : M ^ 3 < Q ^ (8 * N) := by
  have h1 : M < Q ^ D := lt_of_le_of_lt (Nat.le_mul_of_pos_right M hd) h
  calc M ^ 3 < (Q ^ D) ^ 3 := Nat.pow_lt_pow_left h1 (by norm_num)
    _ = Q ^ (3 * D) := by rw [← pow_mul, mul_comm]
    _ ≤ Q ^ (8 * N) := Nat.pow_le_pow_right (by omega) hDN

theorem sl3a_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) < Q ^ 8 := by
  have h2 : Q ^ 2 - 1 < Q ^ 2 := Nat.sub_lt (by positivity) one_pos
  have h3 : Q ^ 3 - 1 < Q ^ 3 := Nat.sub_lt (by positivity) one_pos
  calc Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) < Q ^ 3 * (Q ^ 2 * Q ^ 3) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' h2 h3) (by positivity)
    _ = Q ^ 8 := by ring

theorem sl3b_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) < Q ^ 8 := by
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e : (Q ^ 2 - 1) * (Q ^ 3 + 1) < Q ^ 5 := by
    zify [h1]
    have h5 : (Q : ℤ) ^ 5 = (Q : ℤ) ^ 2 * (Q : ℤ) ^ 3 := by ring
    have : ((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 3 + 1) =
        (Q : ℤ) ^ 5 - ((Q : ℤ) ^ 3 - (Q : ℤ) ^ 2) - 1 := by
      ring
    have h3 : (0 : ℤ) ≤ (Q : ℤ) ^ 3 - (Q : ℤ) ^ 2 := by
      have : (Q : ℤ) ^ 2 ≤ (Q : ℤ) ^ 3 := by exact_mod_cast h2
      linarith
    linarith
  calc Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) < Q ^ 3 * Q ^ 5 :=
        Nat.mul_lt_mul_of_pos_left e (by positivity)
    _ = Q ^ 8 := by ring

theorem sp4_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) < Q ^ 10 := by
  have h2 : Q ^ 2 - 1 < Q ^ 2 := Nat.sub_lt (by positivity) one_pos
  have h4 : Q ^ 4 - 1 < Q ^ 4 := Nat.sub_lt (by positivity) one_pos
  calc Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) < Q ^ 4 * (Q ^ 2 * Q ^ 4) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' h2 h4) (by positivity)
    _ = Q ^ 10 := by ring

theorem u4_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1)) < Q ^ 15 := by
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : Q ^ 4 - 1 < Q ^ 4 := Nat.sub_lt (by positivity) one_pos
  have e : (Q ^ 2 - 1) * (Q ^ 3 + 1) < Q ^ 5 := by
    zify [h1]
    have : ((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 3 + 1) =
        (Q : ℤ) ^ 5 - ((Q : ℤ) ^ 3 - (Q : ℤ) ^ 2) - 1 := by
      ring
    have h3 : (0 : ℤ) ≤ (Q : ℤ) ^ 3 - (Q : ℤ) ^ 2 := by
      have : (Q : ℤ) ^ 2 ≤ (Q : ℤ) ^ 3 := by exact_mod_cast h2
      linarith
    linarith
  calc Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1)) < Q ^ 6 * (Q ^ 5 * Q ^ 4) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' e h4) (by positivity)
    _ = Q ^ 15 := by ring

theorem sz_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 2 * ((Q ^ 2 + 1) * (Q - 1)) < Q ^ 5 := by
  have e : (Q ^ 2 + 1) * (Q - 1) < Q ^ 3 := by
    obtain ⟨t, rfl⟩ : ∃ t, Q = t + 1 := ⟨Q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    nlinarith
  calc Q ^ 2 * ((Q ^ 2 + 1) * (Q - 1)) < Q ^ 2 * Q ^ 3 :=
        Nat.mul_lt_mul_of_pos_left e (by positivity)
    _ = Q ^ 5 := by ring

theorem f4t_lt {Q : ℕ} (hQ : 2 ≤ Q) : ordTwistedF4 Q < Q ^ 26 := by
  have hh : (Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1) < Q ^ 14 := by
    obtain ⟨t, rfl⟩ : ∃ t, Q = t + 2 := ⟨Q - 2, by omega⟩
    have h4 : 1 ≤ (t + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h1 : 1 ≤ t + 2 := by omega
    zify [h4, h1]
    have : (0 : ℤ) < ((t : ℤ) + 2) ^ 14 - (((t : ℤ) + 2) ^ 6 + 1) * (((t : ℤ) + 2) ^ 4 - 1) *
        (((t : ℤ) + 2) ^ 3 + 1) * ((t : ℤ) + 2 - 1) := by
      ring_nf
      positivity
    linarith
  unfold ordTwistedF4
  calc Q ^ 12 * (Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1)
      = Q ^ 12 * ((Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1)) := by ring
    _ < Q ^ 12 * Q ^ 14 := Nat.mul_lt_mul_of_pos_left hh (by positivity)
    _ = Q ^ 26 := by ring

end CFSG.RankThree.PartTwo.Sec4.HeringPin
