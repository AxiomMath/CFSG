module

public import CFSG.Quasithin.H13.L32A511Qa

public section

namespace CFSG.Quasithin.H13.Q511

theorem nsmul_eq_self_of_mod {M : Type*} [AddCommGroup M] {p : ℕ} (hexp : ∀ q : M, p • q = 0)
    {n : ℕ} (hn : n % p = 1) (a : M) : n • a = a := by
  have h : (p * (n / p)) • a = 0 := by rw [mul_comm, ← smul_smul, hexp, smul_zero]
  rw [← Nat.div_add_mod n p, hn, add_nsmul, h, zero_add, one_nsmul]

theorem exists_mul_mod_eq_one {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n) :
    ∃ k : ℕ, n * k % p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine ⟨((n : ZMod p)⁻¹).val, ?_⟩
  have h1 : ((n * ((n : ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hn0]
  rw [← ZMod.val_natCast, h1, ZMod.val_one]

theorem eq_zero_of_nsmul_eq_zero {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ q : M, p • q = 0) {n : ℕ} (hn : ¬ p ∣ n) {a : M} (h : n • a = 0) : a = 0 := by
  obtain ⟨k, hk⟩ := exists_mul_mod_eq_one hp hn
  have e : (n * k) • a = k • (n • a) := by rw [mul_comm, ← smul_smul]
  rw [← nsmul_eq_self_of_mod hexp hk a, e, h, smul_zero]

theorem exists_vec {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hexp : ∀ q : M, p • q = 0) (X S C : M →+ M) (hX3 : ∀ q, X (X (X q)) = q)
    (hS2 : ∀ q, S (S q) = q) (hC2 : ∀ q, C (C q) = q) (hSX : ∀ q, S (X q) = X (X (S q)))
    (hCX : ∀ q, C (X q) = X (C q)) (hCS : ∀ q, C (S q) = S (C q)) {q₀ : M}
    (hq₀ : X q₀ ≠ q₀) :
    ∃ m : M, m ≠ 0 ∧ S m = -m ∧ (C m = m ∨ C m = -m) ∧ m + X m + X (X m) = 0 ∧
      ∀ k : ℕ, X m ≠ k • m := by
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h3 : ∀ a : M, 3 • a = 0 → a = 0 := fun a h => eq_zero_of_nsmul_eq_zero hp hexp hp3 h
  have hNX : ∀ q, X (q + X q + X (X q)) = q + X q + X (X q) := by
    intro q
    rw [map_add, map_add, hX3]
    abel
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M, m₁ = 2 • q₀ - X q₀ - X (X q₀) := ⟨_, rfl⟩
  have hN₁ : m₁ + X m₁ + X (X m₁) = 0 := by
    rw [hm₁]
    simp only [map_sub, map_nsmul, hX3]
    abel
  have hX₁ : X m₁ ≠ m₁ := by
    intro h
    have h1 : 3 • m₁ = 0 := by
      have e : m₁ + X m₁ + X (X m₁) = 3 • m₁ := by rw [h, h]; abel
      rw [← e, hN₁]
    have hm0 : 2 • q₀ - X q₀ - X (X q₀) = 0 := by rw [← hm₁]; exact h3 _ h1
    have h4 : 3 • q₀ = q₀ + X q₀ + X (X q₀) := by
      have e : 3 • q₀ = (2 • q₀ - X q₀ - X (X q₀)) + (q₀ + X q₀ + X (X q₀)) := by abel
      rw [e, hm0, zero_add]
    have h5 : X (3 • q₀) = 3 • q₀ := by rw [h4, hNX]
    rw [map_nsmul] at h5
    apply hq₀
    have : 3 • (X q₀ - q₀) = 0 := by rw [nsmul_sub, h5, sub_self]
    exact sub_eq_zero.mp (h3 _ this)
  have hSN : ∀ q, q + X q + X (X q) = 0 → S q + X (S q) + X (X (S q)) = 0 := by
    intro q hq
    have e1 : X (S q) = S (X (X q)) := by
      have := hSX (X (X q))
      rw [hX3] at this
      rw [this, hX3]
    have e2 : X (X (S q)) = S (X q) := (hSX q).symm
    rw [e2, e1, ← map_add, ← map_add, add_right_comm, hq, map_zero]
  obtain ⟨m₂, hm₂0, hSm₂, hNm₂⟩ : ∃ m₂ : M, m₂ ≠ 0 ∧ S m₂ = -m₂ ∧
      m₂ + X m₂ + X (X m₂) = 0 := by
    by_cases hs : S m₁ = m₁
    · have e1 : S (X m₁) = X (X m₁) := by rw [hSX, hs]
      have e2 : S (X (X m₁)) = X m₁ := by rw [hSX, e1, hX3]
      refine ⟨X m₁ - X (X m₁), ?_, ?_, ?_⟩
      · intro h
        apply hX₁
        have h1 : X m₁ = X (X m₁) := sub_eq_zero.mp h
        have h2 : X (X m₁) = X (X (X m₁)) := congrArg X h1
        rw [hX3] at h2
        rw [h1, h2]
      · rw [map_sub, e1, e2, neg_sub]
      · simp only [map_sub, hX3]
        abel
    · refine ⟨m₁ - S m₁, ?_, ?_, ?_⟩
      · intro h
        exact hs (sub_eq_zero.mp h).symm
      · rw [map_sub, hS2]
        abel
      · have h1 := hSN m₁ hN₁
        have e : m₁ - S m₁ + X (m₁ - S m₁) + X (X (m₁ - S m₁)) =
            (m₁ + X m₁ + X (X m₁)) - (S m₁ + X (S m₁) + X (X (S m₁))) := by
          simp only [map_sub]
          abel
        rw [e, hN₁, h1, sub_zero]
  obtain ⟨m, hm0, hSm, hCm, hNm⟩ : ∃ m : M, m ≠ 0 ∧ S m = -m ∧ (C m = m ∨ C m = -m) ∧
      m + X m + X (X m) = 0 := by
    by_cases hc : C m₂ = -m₂
    · exact ⟨m₂, hm₂0, hSm₂, Or.inr hc, hNm₂⟩
    · refine ⟨m₂ + C m₂, ?_, ?_, Or.inl ?_, ?_⟩
      · intro h
        exact hc (eq_neg_of_add_eq_zero_right h)
      · rw [map_add, hSm₂, ← hCS, hSm₂, map_neg]
        abel
      · rw [map_add, hC2, add_comm]
      · have e : m₂ + C m₂ + X (m₂ + C m₂) + X (X (m₂ + C m₂)) =
            (m₂ + X m₂ + X (X m₂)) + C (m₂ + X m₂ + X (X m₂)) := by
          simp only [map_add, hCX]
          abel
        rw [e, hNm₂, map_zero, add_zero]
  refine ⟨m, hm0, hSm, hCm, hNm, fun k hk => ?_⟩
  have h1 : S (X m) = -(k • m) := by rw [hk, map_nsmul, hSm, smul_neg]
  have h2 : S (X m) = -((k * k) • m) := by
    rw [hSX, hSm, map_neg, map_neg, hk, map_nsmul, hk, smul_smul]
  have h3' : (k * k) • m = k • m := neg_injective (h2.symm.trans h1)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · apply hm0
    rw [← hX3 m, hk, zero_nsmul, map_zero, map_zero]
  · have hle : k ≤ k * k := Nat.le_mul_self k
    have h4 : (k * k - k) • m = 0 := by rw [sub_nsmul m hle, h3', add_neg_cancel]
    have h5 : p ∣ k * (k - 1) := by
      by_contra hcon
      apply hm0
      refine eq_zero_of_nsmul_eq_zero hp hexp ?_ h4
      rwa [Nat.mul_sub_one] at hcon
    rcases (Nat.Prime.dvd_mul hp).mp h5 with h6 | h6
    · apply hm0
      obtain ⟨t, rfl⟩ := h6
      rw [← hX3 m, hk, mul_comm, ← smul_smul, hexp, smul_zero, map_zero, map_zero]
    · apply hm0
      obtain ⟨t, ht⟩ := h6
      have h7 : k % p = 1 := by
        have hk' : k = 1 + p * t := by omega
        rw [hk', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.one_lt]
      rw [nsmul_eq_self_of_mod hexp h7] at hk
      apply h3
      have : m + X m + X (X m) = 3 • m := by rw [hk, hk]; abel
      rw [← this, hNm]

end CFSG.Quasithin.H13.Q511
