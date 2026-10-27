module

public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem zpow_apply_eq_of_apply_eq (ψ : K ≃+* K) {a : K} (h : ψ a = a) (j : ℤ) : (ψ ^ j) a = a := by
  induction j using Int.induction_on with
  | zero => simp
  | succ j ih =>
    rw [zpow_add_one, RingAut.mul_apply, h, ih]
  | pred j ih =>
    have h' : ψ⁻¹ a = a := by
      have h1 := RingEquiv.symm_apply_apply ψ a
      rw [h] at h1
      exact h1
    rw [zpow_sub_one, RingAut.mul_apply, h', ih]

theorem card_pow_fixed {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n)
    (hK : Nat.card K = 2 ^ n) : Nat.card {a : K // a ^ 2 ^ m = a} = 2 ^ m := by
  obtain ⟨φ, hφ, hord, -, -, hA⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK
  obtain ⟨-, S, hS, hcard⟩ := hA (Subgroup.zpowers (φ ^ m))
  have hcardA : Nat.card (Subgroup.zpowers (φ ^ m)) = n / m := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by omega) (hord ▸ hmn), hord]
  have hset : (S : Set K) = {a | a ^ 2 ^ m = a} := by
    rw [hS]
    ext a
    constructor
    · intro h
      have h1 := h (φ ^ m) (Subgroup.mem_zpowers _)
      rwa [ringAut_pow_apply_of_frobenius hφ] at h1
    · intro h τ hτ
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
      refine zpow_apply_eq_of_apply_eq _ ?_ j
      rw [ringAut_pow_apply_of_frobenius hφ]
      exact h
  have hdiv : n / (n / m) = m := Nat.div_div_self hmn (by omega)
  rw [hcardA, hdiv] at hcard
  have hS' : ∀ a : K, a ∈ S ↔ a ^ 2 ^ m = a := fun a => by
    rw [← SetLike.mem_coe, hset]
    rfl
  exact ((Nat.card_congr (Equiv.subtypeEquivRight hS')).symm).trans hcard

variable {σ δ : K ≃+* K} {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (6 * e))
  (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e)) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include he hK hδ in
theorem card_fix_delta : Nat.card {a : K // δ a = a} = 2 ^ (3 * e) := by
  have h := card_pow_fixed (n := 6 * e) (m := 3 * e) (by omega) (by omega) ⟨2, by ring⟩ hK
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [hδ])

theorem pow_pow_mul_eq_self {b : K} {e : ℕ} (h : b ^ 2 ^ e = b) (k : ℕ) :
    b ^ 2 ^ (k * e) = b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, pow_add, pow_mul, ih, h]

include he hK hσ hδ in
theorem card_fix_both : Nat.card {b : K // σ b = b ∧ δ b = b} = 2 ^ e := by
  have h := card_pow_fixed (n := 6 * e) (m := e) (by omega) he ⟨6, by ring⟩ hK
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  rw [hσ, hδ]
  constructor
  · rintro ⟨h1, h2⟩
    calc b ^ 2 ^ e = (b ^ 2 ^ (2 * e)) ^ 2 ^ e := by rw [h1]
      _ = b ^ 2 ^ (3 * e) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ = b := h2
  · intro h1
    exact ⟨pow_pow_mul_eq_self h1 2, pow_pow_mul_eq_self h1 3⟩

end CFSG.Quasithin.H13.F431.D4q.Out
