module

public import CFSG.GroupTheory.PrimeSqDvdCard
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.GroupTheory

theorem exists_prime_order_pair_of_card_gt
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hpow : ∀ x : G, x ^ p = 1) (hcard : p < Nat.card G) :
    ∃ b c : G, orderOf b = p ∧ orderOf c = p ∧ c ∉ Subgroup.zpowers b := by
  classical
  have hp : p.Prime := Fact.out
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by have := hp.two_le; omega)
  obtain ⟨b, hb⟩ := exists_ne (1 : G)
  have hbo : orderOf b = p := orderOf_eq_prime (hpow b) hb
  have hc : ∃ c : G, c ∉ Subgroup.zpowers b := by
    by_contra hn
    push Not at hn
    have hinj : Function.Injective (fun x : G => (⟨x, hn x⟩ : Subgroup.zpowers b)) := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zpowers, hbo] at hle
    omega
  obtain ⟨c, hc⟩ := hc
  have hco : orderOf c = p := by
    apply orderOf_eq_prime (hpow c)
    intro he
    exact hc (he ▸ (Subgroup.zpowers b).one_mem)
  exact ⟨b, c, hbo, hco, hc⟩

theorem dvd_exponents_of_pow_mul_pow_eq_one_of_not_mem_zpowers
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {b c : G}
    (hb : orderOf b = p) (hc : orderOf c = p) (hcb : c ∉ Subgroup.zpowers b)
    {i k : ℕ} (hrel : b ^ i * c ^ k = 1) : p ∣ i ∧ p ∣ k := by
  have hp : p.Prime := Fact.out
  by_cases hck : c ^ k = 1
  · have hb1 : b ^ i = 1 := by simpa only [hck, mul_one] using hrel
    constructor
    · simpa only [hb] using orderOf_dvd_of_pow_eq_one hb1
    · simpa only [hc] using orderOf_dvd_of_pow_eq_one hck
  · have hckb : c ^ k ∈ Subgroup.zpowers b := by
      have he : c ^ k = (b ^ i)⁻¹ := by
        exact mul_eq_one_iff_eq_inv'.mp hrel
      rw [he]
      exact (Subgroup.zpowers b).inv_mem (Subgroup.npow_mem_zpowers b i)
    have hcy := TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp
      (orderOf_eq_prime_iff.mp hc).1 hck (Subgroup.npow_mem_zpowers c k)
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers b := by
      rw [← hcy]
      exact Subgroup.zpowers_le.mpr hckb
    exact False.elim (hcb (hle (by
      simpa only [pow_one] using Subgroup.npow_mem_zpowers c 1)))

end CFSG.GroupTheory
