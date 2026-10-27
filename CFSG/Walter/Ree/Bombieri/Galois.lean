module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.Walter.Ree.Bombieri

variable {K : Type*} [Field K] [Fintype K]

theorem pow_three_pow_mod {k : ℕ} (hK : Fintype.card K = 3 ^ k) (m : ℕ) (x : K) :
    x ^ 3 ^ m = x ^ 3 ^ (m % k) := by
  conv_lhs => rw [← Nat.div_add_mod m k, pow_add, pow_mul, pow_mul,
    ← hK, FiniteField.pow_card_pow]

omit [Fintype K] in
theorem pow_apply_of_eq_frob_pow {σ : K ≃+* K} {b : ℕ} (hσ : ∀ x, σ x = x ^ 3 ^ b) (j : ℕ)
    (x : K) : (σ ^ j) x = x ^ 3 ^ (b * j) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih => rw [pow_succ', RingAut.mul_apply, ih, hσ, ← pow_mul, ← pow_add, mul_add,
      mul_one, add_comm]

theorem eq_one_of_pow_three_pow_eq {k r : ℕ} (hK : Fintype.card K = 3 ^ k) (hk : 2 ≤ k)
    (hr : r < k) (h : ∀ x : K, x ^ 3 ^ r = x ^ 3) : r = 1 := by
  by_contra hr1
  have hne : (3 : ℕ) ^ r ≠ 3 := by
    intro h3
    exact hr1 (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h3))
  have hp : (Polynomial.X ^ 3 ^ r - Polynomial.X ^ 3 : Polynomial K) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id)
      Function.injective_id
    · intro x; simp [h x]
    · rw [hK]
      refine (Polynomial.natDegree_sub_le _ _).trans_lt ?_
      simp only [Polynomial.natDegree_X_pow]
      apply max_lt
      · exact Nat.pow_lt_pow_right (by norm_num) hr
      · calc 3 = 3 ^ 1 := by norm_num
          _ < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have := congrArg (fun p => Polynomial.coeff p (3 ^ r)) hp
  simp [Polynomial.coeff_X_pow, hne] at this

theorem exists_eq_frob_pow [CharP K 3] {k : ℕ} (hK : Fintype.card K = 3 ^ k) (σ : K ≃+* K) :
    ∃ b < k, ∀ x, σ x = x ^ 3 ^ b := by
  let _ : Algebra (ZMod 3) K := ZMod.algebra K 3
  have hfin : Module.finrank (ZMod 3) K = k := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := K)
    rw [hK, ZMod.card] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hcomm : ∀ x : ZMod 3, σ (algebraMap (ZMod 3) K x) = algebraMap (ZMod 3) K x := by
    intro x
    exact congrArg (fun g : ZMod 3 →+* K => g x)
      (RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod 3) K)) (algebraMap (ZMod 3) K))
  let σ' : K ≃ₐ[ZMod 3] K := AlgEquiv.ofRingEquiv (f := σ) hcomm
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 3) K).2 σ'
  refine ⟨n, hfin ▸ n.2, fun x => ?_⟩
  have h1 := congrArg (fun τ : K ≃ₐ[ZMod 3] K => τ x) hn
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    ZMod.card] at h1
  exact h1.symm

theorem coprime_of_generates [CharP K 3] {k b : ℕ} (hK : Fintype.card K = 3 ^ k) (hk : 2 ≤ k)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ b) (hA : ∀ τ : K ≃+* K, ∃ j : ℕ, τ = σ ^ j) :
    Nat.Coprime b k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hA (frobeniusEquiv K 3)
  have h1 : ∀ x : K, x ^ 3 ^ (b * j % k) = x ^ 3 := by
    intro x
    rw [← pow_three_pow_mod hK, ← pow_apply_of_eq_frob_pow hσ, ← hj, frobeniusEquiv_def]
  have h2 := eq_one_of_pow_three_pow_eq hK hk (Nat.mod_lt _ (by omega)) h1
  have h3 : b * j ≡ 1 [MOD k] := by
    unfold Nat.ModEq; rw [h2, Nat.mod_eq_of_lt (by omega)]
  exact Nat.coprime_of_mul_modEq_one j h3

theorem coprime_of_bijective_pow {k e s : ℕ} (hK : Fintype.card K = 3 ^ k)
    (h : ∀ x : K, (x ^ e) ^ s = x) : Nat.Coprime e (3 ^ k - 1) := by
  classical
  by_contra hc
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
  have hpe : p ∣ e := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, hK]; exact hpd.trans (Nat.gcd_dvd_right _ _)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card p hpq
  have hw1 : w ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (hw ▸ hpe)
  have h2 := h (w : K)
  rw [← Units.val_pow_eq_pow_val, hw1, Units.val_one, one_pow] at h2
  have : w = 1 := Units.ext h2.symm
  rw [this, orderOf_one] at hw
  exact hp.one_lt.ne hw

end CFSG.Walter.Ree.Bombieri
