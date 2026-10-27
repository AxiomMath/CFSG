module

public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

section Norm

variable {F : Type} [Field F] [Finite F]

theorem two_le_of_card_eq_sq {Q : ℕ} (hF : Nat.card F = Q ^ 2) : 2 ≤ Q := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have h2 : Q ≤ 1 := by omega
  have h3 : Q ^ 2 ≤ 1 := by nlinarith
  omega

theorem exists_norm_eq {Q : ℕ} (hF : Nat.card F = Q ^ 2) {c : F} (hcQ : c ^ Q = c)
    (hc : c ≠ 0) : ∃ β : F, β ^ Q * β = c := by
  have hQ2 : 2 ≤ Q := two_le_of_card_eq_sq hF
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  let u : Fˣ := Units.mk0 c hc
  obtain ⟨m, hm⟩ : u ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 (hg u)
  have hu : u ^ (Q - 1) = 1 := by
    apply Units.ext
    have h1 : c ^ (Q - 1) * c = 1 * c := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hcQ, one_mul]
    simpa [u] using mul_right_cancel₀ hc h1
  obtain ⟨j, hj⟩ : Q + 1 ∣ m := by
    have h1 : orderOf g ∣ m * (Q - 1) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; simp only [hm]; exact hu)
    rw [hord] at h1
    have e : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
      have h1Q : 1 ≤ Q := by omega
      have h1Q2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1Q, h1Q2]
      ring
    rw [e, mul_comm m] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < Q - 1) h1
  refine ⟨(g : F) ^ j, ?_⟩
  have h1 : (g ^ j) ^ (Q + 1) = u := by
    rw [← pow_mul, mul_comm, ← hj]
    exact hm
  have h2 := congrArg (fun x : Fˣ => (x : F)) h1
  simp only [Units.val_pow_eq_pow_val, u, Units.val_mk0] at h2
  rw [← h2, pow_succ]

end Norm

section CubeRoot

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem three_ne_zero_of_pow_mod_one (hf : 1 ≤ f) (hq : p ^ f % 3 = 1) : (3 : F) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : F) = 0 := by simpa using h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff F p 3).1 h'
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 hdvd
  subst hp3
  have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  omega

theorem exists_cube_root {Q : ℕ} (hF : Nat.card F = Q ^ 2) (hQ : Q % 3 = 1) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 ∧ ω ^ Q = ω := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h1 : 3 ∣ Q - 1 := by omega
    have hQ2 : 2 ≤ Q := two_le_of_card_eq_sq hF
    have e : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
      have h1Q : 1 ≤ Q := by omega
      have h1Q2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1Q, h1Q2]
      ring
    rw [e]
    exact dvd_mul_of_dvd_left h1 _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
  have hw3 : (w : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hw, pow_orderOf_eq_one, Units.val_one]
  have hw1 : (w : F) ≠ 1 := by
    intro h
    have : w = 1 := Units.ext h
    rw [this, orderOf_one] at hw
    omega
  refine ⟨(w : F), ?_, ?_⟩
  · have h0 : ((w : F) - 1) * ((w : F) ^ 2 + (w : F) + 1) = 0 := by
      linear_combination hw3
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hw1)
  · obtain ⟨k, hk⟩ : ∃ k, Q = 3 * k + 1 := ⟨Q / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hw3, one_pow, one_mul]

end CubeRoot

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
