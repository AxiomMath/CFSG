module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.StandardType

@[expose] def psuOrbSize (k : ℕ) : ℕ := if k = 0 then 1 else if k = 5 then 4 else 2

@[expose] def psuRho (q d k : ℕ) : ℕ :=
  if k = 0 ∨ k = 1 ∨ k = 4 then q ^ d + 1 else if k = 3 then q ^ d - 1 else q ^ (2 * d) - 1

private lemma psuGraphArith_rho_A {q d k : ℕ} (hA : k = 0 ∨ k = 1 ∨ k = 4) :
    psuRho q d k = q ^ d + 1 := by
  unfold psuRho
  rw [if_pos hA]

private lemma psuGraphArith_rho_three {q d k : ℕ} (h3 : k = 3) :
    psuRho q d k = q ^ d - 1 := by
  unfold psuRho
  rw [if_neg (by rintro (h | h | h) <;> omega), if_pos h3]

private lemma psuGraphArith_rho_other {q d k : ℕ} (hA : ¬(k = 0 ∨ k = 1 ∨ k = 4)) (h3 : k ≠ 3) :
    psuRho q d k = q ^ (2 * d) - 1 := by
  unfold psuRho
  rw [if_neg hA, if_neg h3]

private lemma psuGraphArith_two_le_sq {q : ℕ} (hq : 2 ≤ q) : q + 2 ≤ q ^ 2 := by
  have h1 : q * 2 ≤ q * q := Nat.mul_le_mul_left q hq
  have h2 : q + 2 ≤ q * 2 := by omega
  calc q + 2 ≤ q * 2 := h2
    _ ≤ q * q := h1
    _ = q ^ 2 := by ring

private lemma psuGraphArith_sq_gt {q : ℕ} (hq : 3 ≤ q) : q + 2 < q ^ 2 := by
  have h1 : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have h2 : q + 2 < 3 * q := by omega
  calc q + 2 < 3 * q := h2
    _ ≤ q * q := h1
    _ = q ^ 2 := by ring

private lemma psuGraphArith_rho_ge {q d k : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d)
    (heven : k = 3 → Even d) : q + 1 ≤ psuRho q d k := by
  by_cases hA : k = 0 ∨ k = 1 ∨ k = 4
  · rw [psuGraphArith_rho_A hA]
    have h1 : q ≤ q ^ d := by
      simpa using Nat.pow_le_pow_right (show 0 < q by omega) hd
    omega
  · by_cases h3 : k = 3
    · rw [psuGraphArith_rho_three h3]
      have hd2 : 2 ≤ d := by
        rcases heven h3 with ⟨m, hm⟩
        omega
      have hle : q ^ 2 ≤ q ^ d := Nat.pow_le_pow_right (show 0 < q by omega) hd2
      have h2 : q + 2 ≤ q ^ 2 := psuGraphArith_two_le_sq hq
      omega
    · rw [psuGraphArith_rho_other hA h3]
      have hle : q ^ 2 ≤ q ^ (2 * d) :=
        Nat.pow_le_pow_right (show 0 < q by omega) (by omega : 2 ≤ 2 * d)
      have h2 : q + 2 ≤ q ^ 2 := psuGraphArith_two_le_sq hq
      omega

private lemma psuGraphArith_pow_eq_self {q d : ℕ} (hq : 2 ≤ q) (h : q ^ d = q) : d = 1 := by
  have h' : q ^ d = q ^ 1 := by simpa using h
  exact Nat.pow_right_injective hq h'

private lemma psuGraphArith_rho_eq_A {q d k : ℕ} (hq : 2 ≤ q) (hA : k = 0 ∨ k = 1 ∨ k = 4)
    (h : psuRho q d k = q + 1) : d = 1 := by
  rw [psuGraphArith_rho_A hA] at h
  exact psuGraphArith_pow_eq_self hq (by omega)

private lemma psuGraphArith_rho_eq_C1 {q d k : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d)
    (hk : k = 2 ∨ k = 5) (h : psuRho q d k = q + 1) : q = 2 ∧ d = 1 := by
  have hA : ¬(k = 0 ∨ k = 1 ∨ k = 4) := by rintro (h0 | h1 | h4) <;> omega
  have h3 : k ≠ 3 := by rintro rfl; omega
  rw [psuGraphArith_rho_other hA h3] at h
  have hpow : q ^ (2 * d) = q + 2 := by omega
  have hq2 : q = 2 := by
    by_contra hne
    have hq3 : 3 ≤ q := by omega
    have hgt : q + 2 < q ^ 2 := psuGraphArith_sq_gt hq3
    have hle : q ^ 2 ≤ q ^ (2 * d) :=
      Nat.pow_le_pow_right (show 0 < q by omega) (by omega : 2 ≤ 2 * d)
    omega
  subst hq2
  have h2d : 2 * d = 2 := by
    have h' : (2 : ℕ) ^ (2 * d) = 2 ^ 2 := by rw [hpow]; norm_num
    exact Nat.pow_right_injective (show (2 : ℕ) ≤ 2 by norm_num) h'
  omega

private lemma psuGraphArith_rho_eq_C2 {q d k : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (heven : Even d)
    (h3 : k = 3) (h : psuRho q d k = q + 1) : q = 2 ∧ d = 2 := by
  rw [psuGraphArith_rho_three h3] at h
  have hpow : q ^ d = q + 2 := by omega
  have hd2 : 2 ≤ d := by rcases heven with ⟨m, hm⟩; omega
  have hq2 : q = 2 := by
    by_contra hne
    have hq3 : 3 ≤ q := by omega
    have hgt : q + 2 < q ^ 2 := psuGraphArith_sq_gt hq3
    have hle : q ^ 2 ≤ q ^ d := Nat.pow_le_pow_right (show 0 < q by omega) hd2
    omega
  subst hq2
  have hd_eq : d = 2 := by
    have h' : (2 : ℕ) ^ d = 2 ^ 2 := by rw [hpow]; norm_num
    exact Nat.pow_right_injective (show (2 : ℕ) ≤ 2 by norm_num) h'
  exact ⟨rfl, hd_eq⟩

theorem psuGraph_arith {ι : Type} (q n f : ℕ) (hq : q = 2 ^ f) (hf : 1 ≤ f)
    (R : Finset ι) (kind d rk : ι → ℕ)
    (hkind : ∀ r ∈ R, kind r ≤ 5) (hd : ∀ r ∈ R, 1 ≤ d r)
    (heven : ∀ r ∈ R, kind r = 3 → Even (d r))
    (hn : n = ∑ r ∈ R, psuOrbSize (kind r) * rk r)
    (hcount : ∑ r ∈ R.filter (fun r => d r = 1), psuOrbSize (kind r) ≤ q ^ 2 - 1)
    (hbound : ∏ r ∈ R, psuRho q (d r) (kind r) ≤ (q + 1) * Nat.gcd n (q + 1))
    (h0 : ∃ r ∈ R, (kind r = 0 ∨ kind r = 2) ∧ rk r = 2 * d r ∧ (kind r = 0 → 4 ≤ q ^ d r))
    (h1 : ∃ r ∈ R, kind r ≠ 0 ∧ kind r ≠ 2)
    (hno : ∀ r ∈ R, (kind r = 3 ∨ kind r = 4 ∨ kind r = 5) → rk r = d r)
    (hno1 : ∀ r ∈ R, kind r = 1 → 4 ≤ q ^ d r → rk r = d r) : False := by
  classical
  obtain ⟨r0, hr0R, hr0kind, hr0rk, hr0q⟩ := h0
  obtain ⟨r1, hr1R, hr1a, hr1b⟩ := h1
  have hr10 : r0 ≠ r1 := by
    rintro rfl
    rcases hr0kind with h | h
    · exact hr1a h
    · exact hr1b h
  have hq2 : 2 ≤ q := by
    rw [hq]
    simpa using Nat.pow_le_pow_right (show 0 < (2 : ℕ) by norm_num) hf
  let ρ : ι → ℕ := fun r => psuRho q (d r) (kind r)
  have hbound' : ∏ r ∈ R, ρ r ≤ (q + 1) * Nat.gcd n (q + 1) := hbound
  have hρ0 : q + 1 ≤ ρ r0 :=
    psuGraphArith_rho_ge hq2 (hd r0 hr0R) (fun hk => heven r0 hr0R hk)
  have hρ1 : q + 1 ≤ ρ r1 :=
    psuGraphArith_rho_ge hq2 (hd r1 hr1R) (fun hk => heven r1 hr1R hk)
  have hrest_ge : 1 ≤ ∏ r ∈ (R.erase r0).erase r1, ρ r := by
    apply Finset.one_le_prod
    intro r hr
    have hrR : r ∈ R := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
    exact le_trans (by omega : 1 ≤ q + 1)
      (psuGraphArith_rho_ge hq2 (hd r hrR) (fun hk => heven r hrR hk))
  have hprod_eq : ∏ r ∈ R, ρ r = ρ r0 * ρ r1 * ∏ r ∈ (R.erase r0).erase r1, ρ r := by
    rw [← Finset.mul_prod_erase R ρ hr0R,
      ← Finset.mul_prod_erase (R.erase r0) ρ
        (Finset.mem_erase.mpr ⟨fun h => hr10 h.symm, hr1R⟩)]
    ring
  have hprod_ge : ρ r0 * ρ r1 ≤ ∏ r ∈ R, ρ r := by
    rw [hprod_eq]
    calc ρ r0 * ρ r1 = ρ r0 * ρ r1 * 1 := (mul_one _).symm
      _ ≤ ρ r0 * ρ r1 * ∏ r ∈ (R.erase r0).erase r1, ρ r :=
        Nat.mul_le_mul_left _ hrest_ge
  have hgcd_le : (q + 1) * Nat.gcd n (q + 1) ≤ (q + 1) * (q + 1) :=
    Nat.mul_le_mul_left _ (Nat.gcd_le_right n (by omega))
  have hprod01_le : (q + 1) * (q + 1) ≤ ρ r0 * ρ r1 := Nat.mul_le_mul hρ0 hρ1
  have hprod_eq2 : ∏ r ∈ R, ρ r = (q + 1) * (q + 1) := by
    apply le_antisymm
    · calc ∏ r ∈ R, ρ r ≤ (q + 1) * Nat.gcd n (q + 1) := hbound'
        _ ≤ (q + 1) * (q + 1) := hgcd_le
    · exact le_trans hprod01_le hprod_ge
  have hprod01_ge : ρ r0 * ρ r1 ≤ (q + 1) * (q + 1) := hprod_eq2 ▸ hprod_ge
  have hprod01 : ρ r0 * ρ r1 = (q + 1) * (q + 1) := le_antisymm hprod01_ge hprod01_le
  have hρ0_eq : ρ r0 = q + 1 := by
    have h1 : ρ r0 * (q + 1) ≤ (q + 1) * (q + 1) := by
      calc ρ r0 * (q + 1) ≤ ρ r0 * ρ r1 := Nat.mul_le_mul_left _ hρ1
        _ ≤ (q + 1) * (q + 1) := hprod01_ge
    exact le_antisymm (Nat.le_of_mul_le_mul_right h1 (by omega)) hρ0
  have hρ1_eq : ρ r1 = q + 1 := by
    have h1 : ρ r1 * (q + 1) ≤ (q + 1) * (q + 1) := by
      calc ρ r1 * (q + 1) ≤ ρ r1 * ρ r0 := Nat.mul_le_mul_left _ hρ0
        _ = ρ r0 * ρ r1 := Nat.mul_comm _ _
        _ ≤ (q + 1) * (q + 1) := hprod01_ge
    exact le_antisymm (Nat.le_of_mul_le_mul_right h1 (by omega)) hρ1
  have hrest_eq : (∏ r ∈ (R.erase r0).erase r1, ρ r) = 1 := by
    have h : (q + 1) * (q + 1) * (∏ r ∈ (R.erase r0).erase r1, ρ r) =
        (q + 1) * (q + 1) := by
      rw [← hprod01, ← hprod_eq, hprod_eq2]
      exact hprod01.symm
    exact Nat.eq_of_mul_eq_mul_left (mul_pos (by omega : 0 < q + 1) (by omega : 0 < q + 1))
      (by rw [mul_one]; exact h)
  have hsub : R ⊆ {r0, r1} := by
    intro x hx
    by_cases hx0 : x = r0
    · simp [hx0]
    by_cases hx1 : x = r1
    · simp [hx1]
    exfalso
    have hxrest : x ∈ (R.erase r0).erase r1 :=
      Finset.mem_erase.mpr ⟨hx1, Finset.mem_erase.mpr ⟨hx0, hx⟩⟩
    have hxR : x ∈ R := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxrest)
    have hle : ρ x ≤ ∏ r ∈ (R.erase r0).erase r1, ρ r := by
      apply Finset.single_le_prod
      · intro r hr
        have hrR : r ∈ R := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
        exact le_trans (by omega : 1 ≤ q + 1)
          (psuGraphArith_rho_ge hq2 (hd r hrR) (fun hk => heven r hrR hk))
      · exact hxrest
    rw [hrest_eq] at hle
    have h3 : 3 ≤ ρ x := le_trans (by omega : 3 ≤ q + 1)
      (psuGraphArith_rho_ge hq2 (hd x hxR) (fun hk => heven x hxR hk))
    omega
  have hsub2 : ({r0, r1} : Finset ι) ⊆ R := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hr0R
    · exact hr1R
  have hReq : R = {r0, r1} := le_antisymm hsub hsub2
  have hn' : n = psuOrbSize (kind r0) * rk r0 + psuOrbSize (kind r1) * rk r1 := by
    rw [hn, hReq, Finset.sum_pair hr10]
  have hcount_lb : ∀ (hd0 : d r0 = 1) (hd1 : d r1 = 1),
      psuOrbSize (kind r0) + psuOrbSize (kind r1) ≤ q ^ 2 - 1 := by
    intro hd0 hd1
    have hsubf : ({r0, r1} : Finset ι) ⊆ R.filter (fun r => d r = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hr0R, hd0⟩
      · exact Finset.mem_filter.mpr ⟨hr1R, hd1⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg
      (s := ({r0, r1} : Finset ι)) (t := R.filter (fun r => d r = 1))
      (f := fun r => psuOrbSize (kind r)) hsubf (fun i _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hr10] at h1
    exact le_trans h1 hcount
  have hgcd_eq : Nat.gcd n (q + 1) = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < q + 1 by omega)
    exact le_antisymm hgcd_le (le_trans hprod01_le (le_trans hprod_ge hbound'))
  have hqcase : q = 2 ∨ 4 ≤ q := by
    rcases (by omega : f = 1 ∨ 2 ≤ f) with hf1 | hf2
    · left; rw [hq, hf1]; norm_num
    · right
      rw [hq]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (show 0 < (2 : ℕ) by norm_num) hf2
  rcases hqcase with hq_eq | hq_ge
  ·
    have hkind0 : kind r0 = 2 := by
      rcases hr0kind with h | h
      · exfalso
        have hd0 : d r0 = 1 := psuGraphArith_rho_eq_A hq2 (Or.inl h) hρ0_eq
        have h4 := hr0q h
        rw [hd0, pow_one] at h4
        omega
      · exact h
    have hd0 : d r0 = 1 := (psuGraphArith_rho_eq_C1 hq2 (hd r0 hr0R) (Or.inl hkind0) hρ0_eq).2
    have hrk0 : rk r0 = 2 := by rw [hr0rk, hd0]
    have hkind1 : kind r1 = 1 ∨ kind r1 = 3 ∨ kind r1 = 4 ∨ kind r1 = 5 := by
      have := hkind r1 hr1R
      omega
    have hdvd : q + 1 ∣ n := by
      rw [← hgcd_eq]
      exact Nat.gcd_dvd_left n (q + 1)
    have ho0 : psuOrbSize (kind r0) = 2 := by rw [hkind0]; unfold psuOrbSize; simp
    rcases hkind1 with h1k | h3k | h4k | h5k
    · have hd1 : d r1 = 1 := psuGraphArith_rho_eq_A hq2 (Or.inr (Or.inl h1k)) hρ1_eq
      have hlb := hcount_lb hd0 hd1
      rw [hq_eq] at hlb
      norm_num at hlb
      have ho1 : psuOrbSize (kind r1) = 2 := by rw [h1k]; unfold psuOrbSize; simp
      rw [ho0, ho1] at hlb
      omega
    · have hd1 : d r1 = 2 :=
        (psuGraphArith_rho_eq_C2 hq2 (hd r1 hr1R) (heven r1 hr1R h3k) h3k hρ1_eq).2
      have hrk1 : rk r1 = 2 := by rw [hno r1 hr1R (Or.inl h3k), hd1]
      have hn8 : n = 8 := by
        rw [hn']
        have ho1 : psuOrbSize (kind r1) = 2 := by rw [h3k]; unfold psuOrbSize; simp
        rw [ho0, ho1, hrk0, hrk1]
      rw [hq_eq, hn8] at hdvd
      exact (by norm_num : ¬((2 : ℕ) + 1 ∣ 8)) hdvd
    · have hd1 : d r1 = 1 := psuGraphArith_rho_eq_A hq2 (Or.inr (Or.inr h4k)) hρ1_eq
      have hlb := hcount_lb hd0 hd1
      rw [hq_eq] at hlb
      norm_num at hlb
      have ho1 : psuOrbSize (kind r1) = 2 := by rw [h4k]; unfold psuOrbSize; simp
      rw [ho0, ho1] at hlb
      omega
    · have hd1 : d r1 = 1 :=
        (psuGraphArith_rho_eq_C1 hq2 (hd r1 hr1R) (Or.inr h5k) hρ1_eq).2
      have hlb := hcount_lb hd0 hd1
      rw [hq_eq] at hlb
      norm_num at hlb
      have ho1 : psuOrbSize (kind r1) = 4 := by rw [h5k]; unfold psuOrbSize; simp
      rw [ho0, ho1] at hlb
      omega
  ·
    have hkind0 : kind r0 = 0 := by
      rcases hr0kind with h | h
      · exact h
      · exfalso
        have := (psuGraphArith_rho_eq_C1 hq2 (hd r0 hr0R) (Or.inl h) hρ0_eq).1
        omega
    have hd0 : d r0 = 1 := psuGraphArith_rho_eq_A hq2 (Or.inl hkind0) hρ0_eq
    have hrk0 : rk r0 = 2 := by rw [hr0rk, hd0]
    have ho0 : psuOrbSize (kind r0) = 1 := by rw [hkind0]; unfold psuOrbSize; simp
    have hkind1 : kind r1 = 1 ∨ kind r1 = 4 := by
      have hle5 := hkind r1 hr1R
      rcases (by omega : kind r1 = 1 ∨ kind r1 = 3 ∨ kind r1 = 4 ∨ kind r1 = 5) with
        h1k | h3k | h4k | h5k
      · exact Or.inl h1k
      · exfalso
        have := (psuGraphArith_rho_eq_C2 hq2 (hd r1 hr1R) (heven r1 hr1R h3k) h3k hρ1_eq).1
        omega
      · exact Or.inr h4k
      · exfalso
        have := (psuGraphArith_rho_eq_C1 hq2 (hd r1 hr1R) (Or.inr h5k) hρ1_eq).1
        omega
    have hd1 : d r1 = 1 := by
      rcases hkind1 with h | h
      · exact psuGraphArith_rho_eq_A hq2 (Or.inr (Or.inl h)) hρ1_eq
      · exact psuGraphArith_rho_eq_A hq2 (Or.inr (Or.inr h)) hρ1_eq
    have hrk1 : rk r1 = 1 := by
      rcases hkind1 with h | h
      · have h4 : 4 ≤ q ^ d r1 := by rw [hd1, pow_one]; exact hq_ge
        rw [hno1 r1 hr1R h h4, hd1]
      · rw [hno r1 hr1R (Or.inr (Or.inl h)), hd1]
    have ho1 : psuOrbSize (kind r1) = 2 := by
      rcases hkind1 with h | h <;> (rw [h]; unfold psuOrbSize; simp)
    have hn4 : n = 4 := by
      rw [hn', ho0, ho1, hrk0, hrk1]
    have hdvd : q + 1 ∣ n := by
      rw [← hgcd_eq]
      exact Nat.gcd_dvd_left n (q + 1)
    have hle : q + 1 ≤ n := Nat.le_of_dvd (by omega) hdvd
    omega

end CFSG.StandardType
