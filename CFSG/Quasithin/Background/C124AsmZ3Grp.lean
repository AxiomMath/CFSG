module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.C124

theorem exists_generator_three {M : Type*} [Group M] {Ys : Subgroup M} (hc : Nat.card Ys = 3) :
    ∃ x : M, x ∈ Ys ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ Ys = Subgroup.zpowers x := by
  have hfin : Finite Ys := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial Ys := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨x₁, hx₁⟩ := exists_ne (1 : Ys)
  have hx1 : (x₁ : M) ≠ 1 := fun h => hx₁ (Subtype.ext h)
  have hdvd : orderOf (x₁ : M) ∣ 3 := hc ▸ Subgroup.orderOf_dvd_natCard Ys x₁.2
  have hord : orderOf (x₁ : M) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left (fun h => hx1 (orderOf_eq_one_iff.1 h))
  refine ⟨x₁, x₁.2, by simpa [hord] using pow_orderOf_eq_one (x₁ : M), hx1, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 x₁.2)
  rw [Nat.card_zpowers, hord, hc]

theorem conj_dichotomy {M : Type*} [Group M] {x c : M} (h3 : x ^ 3 = 1) (h1 : x ≠ 1)
    (hc : c * x * c⁻¹ ∈ Subgroup.zpowers x) : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hord : orderOf x = 3 := orderOf_eq_prime h3 h1
  have hmod : x ^ (k % 3) = x ^ k := by
    have := zpow_mod_orderOf x k
    rwa [hord, Nat.cast_ofNat] at this
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hk' : x ^ (k % 3) = c * x * c⁻¹ := hmod.trans hk
  rcases hcases with h | h | h
  · exfalso
    apply h1
    rw [h, zpow_zero] at hk'
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [← hk']; group
  · left
    rw [h, zpow_one] at hk'
    exact hk'.symm
  · right
    rw [h] at hk'
    have : x ^ (2 : ℤ) * x = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← pow_succ, h3]
    exact hk'.symm.trans (eq_inv_of_mul_eq_one_left this)

theorem mem_normalizer_zpowers {M : Type*} [Group M] {x c : M}
    (hc : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) :
    c ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup M) : Set M) := by
  have key : ∀ (c : M), (c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) →
      ∀ z ∈ Subgroup.zpowers x, c * z * c⁻¹ ∈ Subgroup.zpowers x := by
    intro c hc z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← conj_zpow]
    rcases hc with h | h <;> rw [h]
    · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
    · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) _
  have hinv : c⁻¹ * x * c⁻¹⁻¹ = x ∨ c⁻¹ * x * c⁻¹⁻¹ = x⁻¹ := by
    rcases hc with h | h
    · left
      have e : c⁻¹ * x * c⁻¹⁻¹ = c⁻¹ * (c * x * c⁻¹) * c := by rw [h, inv_inv]
      rw [e]
      group
    · right
      have h' : c⁻¹ * x⁻¹ * c = x := by
        calc c⁻¹ * x⁻¹ * c = c⁻¹ * (c * x * c⁻¹) * c := by rw [h]
          _ = x := by group
      calc c⁻¹ * x * c⁻¹⁻¹ = (c⁻¹ * x⁻¹ * c)⁻¹ := by group
        _ = x⁻¹ := by rw [h']
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key c hc y, fun hy => ?_⟩
  have := key c⁻¹ hinv _ hy
  simpa [mul_assoc] using this

theorem ne_inv_of_order_three {M : Type*} [Group M] {x : M} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x ≠ x⁻¹ := by
  intro h
  apply h1
  have h2 : x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel x
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

end CFSG.Quasithin.C124
