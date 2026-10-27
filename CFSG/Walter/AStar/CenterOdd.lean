module

import Mathlib.GroupTheory.Transfer
public import CFSG.Walter.Defs

public section

namespace CFSG.Walter

open scoped IsMulCommutative

theorem odd_card_center_of_perfect {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (hK : HasAbelianSylowTwo K) :
    Odd (Nat.card (Subgroup.center K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra heven
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at heven
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2 heven
  set t : K := (z : K) with ht_def
  have ht : orderOf t = 2 := by rw [ht_def, Subgroup.orderOf_coe, hz]
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, ht]
    exact ⟨1, by norm_num⟩
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have := hK S
  have htS : t ∈ (S : Subgroup K) := hS (Subgroup.mem_zpowers t)
  have hcentral : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * t ^ k * g₀ = t ^ k := by
    intro k g₀
    have hmem : t ^ k ∈ Subgroup.center K := pow_mem z.2 k
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hmem g₀), inv_mul_cancel_left]
  have hV := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup K)) t
    (fun k g₀ _ => hcentral k g₀)
  have hker : t ∈ (MonoidHom.transfer (MonoidHom.id (S : Subgroup K))).ker := by
    have h := Abelianization.commutator_subset_ker
      (MonoidHom.transfer (MonoidHom.id (S : Subgroup K)))
    rw [hperf] at h
    exact h (Subgroup.mem_top t)
  rw [MonoidHom.mem_ker, hV, MonoidHom.id_apply] at hker
  have hpow : t ^ (S : Subgroup K).index = 1 := congrArg Subtype.val hker
  have hdvd : orderOf t ∣ (S : Subgroup K).index := orderOf_dvd_of_pow_eq_one hpow
  rw [ht] at hdvd
  exact S.not_dvd_index hdvd

end CFSG.Walter
