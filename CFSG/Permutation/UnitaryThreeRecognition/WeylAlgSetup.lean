module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgBasic

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] (J : HermitianForm 3 K)

structure SMapHyp (q : ℕ) (F : Coord J → Coord J) (σ : Kˣ →* Kˣ) (h : Coord J → Kˣ) :
    Prop where
  card : Nat.card K = q ^ 2
  conj_pow : ∀ x, J.conj x = x ^ q
  q_odd : Odd q
  q_ge : 3 ≤ q
  coprime : Nat.Coprime 3 (q + 1)
  F_ne : ∀ c, c ≠ 1 → F c ≠ 1
  F_F : ∀ c, c ≠ 1 → F (F c) = c
  σσ : ∀ k, σ (σ k) = k
  σfix : ∀ k, σ k = k ↔ (k : K) ^ (q + 1) = 1
  F_torus : ∀ k c, c ≠ 1 →
    F (hermitianTorusAction J k c) = hermitianTorusAction J (σ k) (F c)
  F_Z : ∀ c, c ≠ 1 → c.1.1 = 0 → (F c).1.1 = 0
  F_block : ∀ u : Coord J, u.1.1 ≠ 0 → ∀ k k' : Kˣ, (k : K) ^ (q + 1) = 1 →
    (k' : K) ^ (q + 1) = 1 → k ≠ 1 → k' ≠ 1 →
    (F (u⁻¹ * hermitianTorusAction J k u)).1.1 = (F (u⁻¹ * hermitianTorusAction J k' u)).1.1
  F_moufang : ∀ z w, z ≠ 1 → z.1.1 = 0 → w.1.1 ≠ 0 →
    F (z * w) = F z * hermitianTorusAction J (h z) (F ((F z⁻¹)⁻¹ * F w))
  h_rel : ∀ z, z ≠ 1 → z.1.1 = 0 → hermitianTorusAction J (h z) (F (F z⁻¹)⁻¹) = (F z)⁻¹
  h_torus : ∀ k z, z ≠ 1 → z.1.1 = 0 → h (hermitianTorusAction J k z) = σ k * h z * k⁻¹

variable {J} [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem two_ne_zero' : (2 : K) ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro h2
  have hchar : ringChar K = 2 := by
    have := ringChar.dvd (show ((2 : ℕ) : K) = 0 by exact_mod_cast h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, H.card, hchar] at hn
  have hev : Even (q ^ 2) := by rw [hn]; exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  exact (Nat.not_even_iff_odd.mpr (H.q_odd.pow)) hev

theorem units_pow_sq' (k : Kˣ) : k ^ (q * q) = k := units_pow_sq H.card k

omit [Finite K] in
theorem nrm_eq_pow' (x : K) : nrm J x = x ^ (q + 1) := nrm_eq_pow J H.conj_pow x

theorem sigma_mul_pow_sq (k : Kˣ) : (σ k * k ^ q) ^ 2 = 1 := by
  refine sq_eq_one_of_involutive (by have := H.q_ge; omega) H.units_pow_sq' σ H.σσ ?_ k
  intro x
  rw [H.σfix x]
  constructor
  · intro hx; exact Units.ext (by simpa using hx)
  · intro hx; simpa using congrArg Units.val hx

theorem sigma_eq (k : Kˣ) :
    ((σ k : K) * J.conj k = 1 ∨ (σ k : K) * J.conj k = -1) := by
  have h1 := congrArg Units.val (H.sigma_mul_pow_sq k)
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one] at h1
  rw [← H.conj_pow] at h1
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h1)

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
