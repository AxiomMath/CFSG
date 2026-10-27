module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.J4L4

open Equiv

local notation "A₈" => alternatingGroup (Fin 8)

theorem card_alt8 : Nat.card A₈ = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem exists_order_fifteen : ∃ g : A₈, orderOf g = 15 := by
  let σ : Perm (Fin 8) := c[0, 1, 2, 3, 4] * c[5, 6, 7]
  have hs : σ ∈ alternatingGroup (Fin 8) := by
    rw [Perm.mem_alternatingGroup]
    decide +kernel
  refine ⟨⟨σ, hs⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  show orderOf σ = 15
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide +kernel) fun p hp hd => ?_
  have h35 : p = 3 ∨ p = 5 := by
    have h : p ∣ 3 * 5 := hd
    rcases (Nat.Prime.dvd_mul hp).1 h with h3 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5)
  rcases h35 with rfl | rfl <;> decide +kernel

theorem exists_order_five : ∃ g : A₈, orderOf g = 5 := by
  let σ : Perm (Fin 8) := c[0, 1, 2, 3, 4]
  have hs : σ ∈ alternatingGroup (Fin 8) := by
    rw [Perm.mem_alternatingGroup]
    decide +kernel
  refine ⟨⟨σ, hs⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  show orderOf σ = 5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem exists_noncomm : ∃ a b : A₈, a * b ≠ b * a := by
  let σ : Perm (Fin 8) := c[0, 1, 2]
  let τ : Perm (Fin 8) := c[1, 2, 3]
  have h1 : σ ∈ alternatingGroup (Fin 8) := by
    rw [Perm.mem_alternatingGroup]
    decide +kernel
  have h2 : τ ∈ alternatingGroup (Fin 8) := by
    rw [Perm.mem_alternatingGroup]
    decide +kernel
  have hne : σ * τ ≠ τ * σ := by decide +kernel
  exact ⟨⟨σ, h1⟩, ⟨τ, h2⟩, fun h => hne (congrArg Subtype.val h)⟩

theorem card_mulAut : Nat.card (MulAut A₈) = 40320 := by
  have h := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
    (by norm_num)
  rw [← Nat.card_congr (Equiv.ofBijective _ h)]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem card_le_of_isPGroup_mulAut {H : Subgroup (MulAut A₈)} (hH : IsPGroup 2 H) :
    Nat.card H ≤ 128 := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : 2 ^ k ∣ 40320 := hk ▸ card_mulAut ▸ Subgroup.card_subgroup_dvd_card H
  have hk7 : k ≤ 7 := by
    by_contra h
    push Not at h
    have : 2 ^ 8 ∣ 2 ^ k := pow_dvd_pow 2 h
    have := this.trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
    _ = 128 := by norm_num

end CFSG.Quasithin.J4L4
