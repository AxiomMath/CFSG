module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs

public section

namespace CFSG.RepresentationTheory.SL2NatSum

variable {K : Type*} [Field K] {R : Type*} [Ring R] [Algebra K R]

def weightProj (h : R) (N : ℕ) (μ : K) : R :=
  ∑ k ∈ Finset.range N, ((μ⁻¹) ^ k) • h ^ k

theorem pow_mul_eq_smul_mul_pow {h w : R} {s : K}
    (hw : h * w = s • (w * h)) (k : ℕ) :
    h ^ k * w = s ^ k • (w * h ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', mul_assoc, ih, Algebra.mul_smul_comm, ← mul_assoc, hw,
      Algebra.smul_mul_assoc, ← mul_assoc]
    rw [smul_smul, mul_assoc, mul_comm s (s ^ k), ← pow_succ, ← pow_succ']

theorem weightProj_mul_eq_mul_weightProj {N : ℕ} {h w : R} {s μ : K} (hs : s ≠ 0)
    (hw : h * w = s • (w * h)) :
    w * weightProj h N μ = weightProj h N (μ * s) * w := by
  simp only [weightProj]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, pow_mul_eq_smul_mul_pow hw k,
    smul_smul]
  congr 1
  rw [← mul_pow, mul_inv, mul_assoc, inv_mul_cancel₀ hs, mul_one]

private lemma two_pow_orderOf_facts {n : ℕ} (hn : 0 < n) {t : K}
    (ht : orderOf t = 2 ^ n - 1) :
    2 ≤ 2 ^ n ∧ 0 < 2 ^ n - 1 ∧ t ^ (2 ^ n - 1) = 1 ∧ t ≠ 0 := by
  have h2 : 2 ≤ 2 ^ n :=
    Nat.one_lt_pow (n := n) (a := 2) hn.ne' (by decide : 1 < 2)
  have hNpos : 0 < 2 ^ n - 1 := by omega
  have htN : t ^ (2 ^ n - 1) = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have ht_ne : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hNpos.ne'] at htN
    exact zero_ne_one htN
  exact ⟨h2, hNpos, htN, ht_ne⟩

private lemma sum_pow_inv_eq_zero {n : ℕ} (hn : 0 < n) {t : K}
    (ht : orderOf t = 2 ^ n - 1) {k : ℕ} (hk0 : k ≠ 0) (hkN : k < 2 ^ n - 1) :
    ∑ e ∈ Finset.range (2 ^ n - 1), ((t ^ e)⁻¹) ^ k = 0 := by
  obtain ⟨-, hNpos, htN, ht_ne⟩ := two_pow_orderOf_facts hn ht
  have htinvN : (t⁻¹) ^ (2 ^ n - 1) = 1 := by
    rw [inv_pow, htN, inv_one]
  have hxne : (t⁻¹) ^ k ≠ 1 := by
    intro hx
    have htk : t ^ k = 1 := by
      have h := congrArg (fun x : K => x * t ^ k) hx
      rw [← mul_pow, inv_mul_cancel₀ ht_ne, one_pow, one_mul] at h
      exact h.symm
    exact (pow_ne_one_of_lt_orderOf (x := t) hk0 (by rwa [ht])) htk
  have hxN : ((t⁻¹) ^ k) ^ (2 ^ n - 1) = 1 := by
    rw [← pow_mul, mul_comm k (2 ^ n - 1), pow_mul, htinvN, one_pow]
  have hgeom : (∑ e ∈ Finset.range (2 ^ n - 1), ((t⁻¹) ^ k) ^ e) *
      ((t⁻¹) ^ k - 1) = 0 := by
    rw [geom_sum_mul, hxN, sub_self]
  have hzero : ∑ e ∈ Finset.range (2 ^ n - 1), ((t⁻¹) ^ k) ^ e = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hxne)
  have hterm : ∀ e : ℕ, ((t ^ e)⁻¹) ^ k = ((t⁻¹) ^ k) ^ e := by
    intro e
    rw [← inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  simpa only [hterm] using hzero

theorem sum_weightProj_eq_one [CharP K 2] {n : ℕ} (hn : 0 < n) {t : K}
    (ht : orderOf t = 2 ^ n - 1) (h : R) :
    ∑ e ∈ Finset.range (2 ^ n - 1), weightProj h (2 ^ n - 1) (t ^ e) = 1 := by
  obtain ⟨h2, hNpos, -, -⟩ := two_pow_orderOf_facts hn ht
  set N := 2 ^ n - 1 with hN
  have hNpos' : 0 < N := by simpa only [hN] using hNpos
  have hcast : ((N : ℕ) : K) = 1 := by
    rw [hN]
    have hle : 1 ≤ 2 ^ n := by omega
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat]
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [h2K, zero_pow hn.ne', zero_sub, CharTwo.neg_eq, Nat.cast_one]
  have hswap : ∑ e ∈ Finset.range N, weightProj h N (t ^ e)
      = ∑ k ∈ Finset.range N, (∑ e ∈ Finset.range N, ((t ^ e)⁻¹) ^ k) • h ^ k := by
    simp only [weightProj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_smul]
  rw [hswap, Finset.sum_eq_single 0]
  · have hcoeff : (∑ e ∈ Finset.range N, ((t ^ e)⁻¹) ^ (0 : ℕ)) = (N : K) := by
      simp
    rw [hcoeff, hcast]
    simp
  · intro k hk hk0
    have hkN : k < 2 ^ n - 1 := by simpa only [hN] using Finset.mem_range.mp hk
    have hzero := sum_pow_inv_eq_zero hn ht hk0 hkN
    rw [show (∑ e ∈ Finset.range N, ((t ^ e)⁻¹) ^ k) = 0 by
      simpa only [hN] using hzero, zero_smul]
  · intro h0
    exact (h0 (Finset.mem_range.mpr hNpos')).elim

theorem mul_eq_zero_of_shift [CharP K 2] {n : ℕ} (hn : 0 < n) {t : K}
    (ht : orderOf t = 2 ^ n - 1) (h : R) (W : ℕ → R)
    (hW : ∀ j < 2 ^ n, h * W j = (t ^ 2) ^ j • (W j * h))
    (hcomm : ∀ b < n, ∀ c < n, W (2 ^ b) * W (2 ^ c) = W (2 ^ c) * W (2 ^ b))
    (wt : ℕ → Prop)
    (hspec : ∀ e : ℕ, ¬ wt e → ∑ k ∈ Finset.range (2 ^ n - 1), ((t ^ e)⁻¹) ^ k • h ^ k = 0)
    (hsq : ∀ b < n, ∀ c < n, b ≠ c → ∀ e : ℕ, wt e → wt (e + 2 ^ (b + 1)) →
      wt (e + 2 ^ (c + 1)) → wt (e + 2 ^ (b + 1) + 2 ^ (c + 1)) → False) :
    ∀ b < n, ∀ c < n, b ≠ c → W (2 ^ b) * W (2 ^ c) = 0 := by
  intro b hb c hc hbc
  obtain ⟨-, -, -, ht_ne⟩ := two_pow_orderOf_facts hn ht
  set N := 2 ^ n - 1 with hN
  have ht2_ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht_ne
  have hspec' : ∀ e : ℕ, ¬ wt e → weightProj h N (t ^ e) = 0 := hspec
  have hres : ∑ e ∈ Finset.range N, weightProj h N (t ^ e) = 1 := by
    simpa only [hN] using sum_weightProj_eq_one hn (ht.trans hN) h
  have hshift : ∀ d : ℕ, d < n → ∀ μ : K, W (2 ^ d) * weightProj h N μ
      = weightProj h N (μ * (t ^ 2) ^ (2 ^ d)) * W (2 ^ d) := by
    intro d hd μ
    exact weightProj_mul_eq_mul_weightProj (N := N) (h := h) (w := W (2 ^ d))
      (s := (t ^ 2) ^ (2 ^ d)) (μ := μ) (pow_ne_zero _ ht2_ne)
      (hW (2 ^ d) (Nat.pow_lt_pow_right (by decide : 1 < 2) hd))
  have hpow : ∀ a d : ℕ, t ^ a * (t ^ 2) ^ (2 ^ d) = t ^ (a + 2 ^ (d + 1)) := by
    intro a d
    rw [← pow_mul, ← pow_add, pow_succ']
  have hunit : W (2 ^ b) * W (2 ^ c) * (∑ e ∈ Finset.range N, weightProj h N (t ^ e))
      = W (2 ^ b) * W (2 ^ c) := by
    rw [hres, mul_one]
  rw [← hunit, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro e _
  by_cases h1 : wt e
  · by_cases h2' : wt (e + 2 ^ (c + 1))
    · by_cases h3 : wt (e + 2 ^ (b + 1))
      · by_cases h4 : wt (e + 2 ^ (b + 1) + 2 ^ (c + 1))
        · exact (hsq b hb c hc hbc e h1 h3 h2' h4).elim
        · rw [mul_assoc, hshift c hc (t ^ e), hpow e c, ← mul_assoc,
            hshift b hb (t ^ (e + 2 ^ (c + 1))), hpow (e + 2 ^ (c + 1)) b]
          have hexp : e + 2 ^ (c + 1) + 2 ^ (b + 1)
              = e + 2 ^ (b + 1) + 2 ^ (c + 1) := by ac_rfl
          rw [hexp, hspec' _ h4, zero_mul, zero_mul]
      · rw [hcomm b hb c hc, mul_assoc, hshift b hb (t ^ e), hpow e b,
          hspec' _ h3, zero_mul, mul_zero]
    · rw [mul_assoc, hshift c hc (t ^ e), hpow e c, hspec' _ h2', zero_mul, mul_zero]
  · rw [hspec' e h1, mul_zero]

end CFSG.RepresentationTheory.SL2NatSum
