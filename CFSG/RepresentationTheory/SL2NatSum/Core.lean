module

public import CFSG.RepresentationTheory.SL2NatSum.Coeffs
public import CFSG.RepresentationTheory.SL2NatSum.WeightShift
public import CFSG.RepresentationTheory.SL2NatSum.Weights

public section

namespace CFSG.RepresentationTheory.SL2NatSum

theorem mul_eq_zero_of_torus {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {R : Type*} [Ring R] [Algebra K R] {n : ℕ} (hq : Fintype.card K = 2 ^ n)
    (hn : n = 2 ∨ 4 ≤ n) (P : K → R) (hP0 : P 0 = 0)
    (hPadd : ∀ x y, P (x + y) = P x + P y + P x * P y) {t : K} (ht : orderOf t = 2 ^ n - 1)
    (h : R) (hh : ∀ x, h * P x = P (t ^ 2 * x) * h)
    (hspec : ∀ e : ℕ, ¬ IsTorusWt n (e : ZMod (2 ^ n - 1)) →
      ∑ k ∈ Finset.range (2 ^ n - 1), ((t ^ e)⁻¹) ^ k • h ^ k = 0) :
    ∀ x y, P x * P y = 0 := by
  obtain ⟨W, hW, hcomm, hred⟩ :=
    exists_coeff_unipotent hq P hP0 hPadd h (t ^ 2) hh
  have hn2 : 2 ≤ n := by rcases hn with rfl | h4 <;> omega
  have hway : ∀ b < n, ∀ c < n, b ≠ c → W (2 ^ b) * W (2 ^ c) = 0 := by
    refine mul_eq_zero_of_shift (n := n) (by omega) ht h W hW hcomm
      (fun e : ℕ => IsTorusWt n (e : ZMod (2 ^ n - 1))) hspec ?_
    intro b hb c hc hbc e h0 h1 h2 h3
    have hbc' : (2 : ZMod (2 ^ n - 1)) ^ (b + 1) ≠ 2 ^ (c + 1) :=
      two_pow_succ_ne hn2 hb hc hbc
    have h1' : IsTorusWt n ((e : ZMod (2 ^ n - 1)) + 2 ^ (b + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using h1
    have h2' : IsTorusWt n ((e : ZMod (2 ^ n - 1)) + 2 ^ (c + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using h2
    have h3' : IsTorusWt n ((e : ZMod (2 ^ n - 1)) + 2 ^ (b + 1) + 2 ^ (c + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using h3
    exact not_isTorusWt_square hn hbc' h0 h1' h2' h3'
  exact hred hway

end CFSG.RepresentationTheory.SL2NatSum
