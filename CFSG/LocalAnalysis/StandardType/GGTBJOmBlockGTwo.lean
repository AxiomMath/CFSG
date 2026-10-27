module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs

public section

open Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth

variable {p r : ℕ}

theorem exists_odd_pow_pow_two_eq_one {G : Type} [Group G] [Finite G] (w : G) :
    ∃ N : ℕ, Odd N ∧ ∃ e : ℕ, (w ^ N) ^ (2 ^ e) = 1 := by
  obtain ⟨e, N, hN, hwN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  refine ⟨N, hN, e, ?_⟩
  rw [← pow_mul, mul_comm N (2 ^ e), ← hwN, pow_orderOf_eq_one]

theorem pow_odd_conj_eq {G T : Type} [Group G] [Group T] (τ : T →* G) {w : G} {σ : T → T}
    (hσ : ∀ f, w * τ f * w⁻¹ = τ (σ f)) (hσσ : ∀ f, σ (σ f) = f) {N : ℕ} (hN : Odd N)
    (f : T) : w ^ N * τ f * (w ^ N)⁻¹ = τ (σ f) := by
  have hw2 : ∀ g : T, w ^ 2 * τ g * (w ^ 2)⁻¹ = τ g := by
    intro g
    rw [show w ^ 2 * τ g * (w ^ 2)⁻¹ = w * (w * τ g * w⁻¹) * w⁻¹ by
        rw [pow_two, mul_inv_rev]
        simp only [mul_assoc],
      hσ g, hσ (σ g), hσσ g]
  have hpow : ∀ k : ℕ, ∀ g : T, (w ^ 2) ^ k * τ g * ((w ^ 2) ^ k)⁻¹ = τ g := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
        intro g
        rw [pow_succ, mul_inv_rev,
          show (w ^ 2) ^ k * (w ^ 2) * τ g * ((w ^ 2)⁻¹ * ((w ^ 2) ^ k)⁻¹) =
              (w ^ 2) ^ k * ((w ^ 2) * τ g * (w ^ 2)⁻¹) * ((w ^ 2) ^ k)⁻¹ by group,
          hw2 g, ih g]
  obtain ⟨k, hk⟩ := hN
  rw [hk, pow_succ, pow_mul,
    show (w ^ 2) ^ k * w * τ f * ((w ^ 2) ^ k * w)⁻¹ =
        (w ^ 2) ^ k * (w * τ f * w⁻¹) * ((w ^ 2) ^ k)⁻¹ by group,
    hσ f, hpow k (σ f)]

theorem permAut_swap_swap (i k : Fin r) (f : Fin r → Multiplicative (ZMod p)) :
    permAut (Equiv.swap i k) (permAut (Equiv.swap i k) f) = f := by
  funext j
  simp only [permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_self]

theorem permAut_swap_eq_self {i k : Fin r} {f : Fin r → Multiplicative (ZMod p)}
    (h : f i = f k) : permAut (Equiv.swap i k) f = f := by
  funext j
  simp only [permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hji : j = i
  · rw [hji, Equiv.swap_apply_left]
    exact h.symm
  · by_cases hjk : j = k
    · rw [hjk, Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hji hjk]

theorem permAut_swap_dinv_involutive (i k : Fin r) (f : Fin r → Multiplicative (ZMod p)) :
    permAut (Equiv.swap i k) (dinv i k (permAut (Equiv.swap i k) (dinv i k f))) = f := by
  funext j
  simp only [permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hik : i = k
  · rw [hik]
    simp [permAut_apply, Equiv.swap_self, OrthNs.dinv_apply_eq]
  · by_cases hji : j = i
    · rw [hji, Equiv.swap_apply_left, OrthNs.dinv_apply_eq, if_neg hik, if_pos (Or.inr rfl),
        Function.comp_apply, Equiv.swap_apply_right, OrthNs.dinv_apply_eq, if_neg hik,
        if_pos (Or.inl rfl), inv_inv]
    · by_cases hjk : j = k
      · rw [hjk, Equiv.swap_apply_right, OrthNs.dinv_apply_eq, if_neg hik, if_pos (Or.inl rfl),
          Function.comp_apply, Equiv.swap_apply_left, OrthNs.dinv_apply_eq, if_neg hik,
          if_pos (Or.inr rfl), inv_inv]
      · have hnot : ¬ (j = i ∨ j = k) := by
          rintro (h' | h')
          · exact hji h'
          · exact hjk h'
        rw [Equiv.swap_apply_of_ne_of_ne hji hjk, OrthNs.dinv_apply_eq, if_neg hik,
          if_neg hnot, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hji hjk,
          OrthNs.dinv_apply_eq, if_neg hik, if_neg hnot]

theorem permAut_swap_dinv_eq_self {i k : Fin r} (hik : i ≠ k)
    {f : Fin r → Multiplicative (ZMod p)} (h : toAdd (f k) = -toAdd (f i)) :
    permAut (Equiv.swap i k) (dinv i k f) = f := by
  funext j
  simp only [permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hji : j = i
  · rw [hji, Equiv.swap_apply_left, OrthNs.dinv_apply_eq, if_neg hik, if_pos (Or.inr rfl)]
    exact toAdd.injective (by rw [toAdd_inv, h, neg_neg])
  · by_cases hjk : j = k
    · rw [hjk, Equiv.swap_apply_right, OrthNs.dinv_apply_eq, if_neg hik, if_pos (Or.inl rfl)]
      exact toAdd.injective (by rw [toAdd_inv, h])
    · have hnot : ¬ (j = i ∨ j = k) := by
        rintro (h' | h')
        · exact hji h'
        · exact hjk h'
      rw [Equiv.swap_apply_of_ne_of_ne hji hjk, OrthNs.dinv_apply_eq, if_neg hik, if_neg hnot]

theorem ne_of_toAdd_eq_neg [Fact p.Prime] (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0)
    {f : Fin r → Multiplicative (ZMod p)} {i k : Fin r} (hi : toAdd (f i) = a)
    (hk : toAdd (f k) = -a) : i ≠ k := by
  intro hik
  subst hik
  have haeq : a = -a := hi.symm.trans hk
  have h2a : (2 : ZMod p) * a = 0 := (two_mul a).trans (eq_neg_iff_add_eq_zero.mp haeq)
  rcases mul_eq_zero.mp h2a with h2 | ha0
  · have hp : p.Prime := Fact.out
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)))
  · exact ha ha0

end OrthTorus

end CFSG.StandardType

end
