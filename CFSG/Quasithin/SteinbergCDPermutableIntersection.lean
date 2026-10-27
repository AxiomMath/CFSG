module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup
open scoped Pointwise

variable {H : Type*} [Group H]

theorem mem_of_mul_mem_of_coprime {P Q K : Subgroup H}
    (hcop : Nat.Coprime (Nat.card P) (Nat.card Q)) (hPK : P ≤ normalizer (K : Set H)) {p q : H}
    (hp : p ∈ P) (hq : q ∈ Q) (hpq : p * q ∈ K) : p ∈ K ∧ q ∈ K := by
  have hqN : q⁻¹ ∈ normalizer (K : Set H) := by
    have e : q⁻¹ = (p * q)⁻¹ * p := by group
    rw [e]
    exact mul_mem (inv_mem (le_normalizer hpq)) (hPK hp)
  have hpow : ∀ m : ℕ, ∃ x ∈ K, p ^ m = x * q⁻¹ ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem K, by simp⟩
    | succ m ih =>
      obtain ⟨x, hx, he⟩ := ih
      refine ⟨x * (q⁻¹ ^ m * (p * q) * (q⁻¹ ^ m)⁻¹),
        mul_mem hx ((mem_normalizer_iff.mp (pow_mem hqN m) _).mp hpq), ?_⟩
      rw [pow_succ, he]
      group
  obtain ⟨x, hx, he⟩ := hpow (Nat.card P)
  have hpm : p ^ Nat.card P = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨p, hp⟩)
    exact congrArg Subtype.val h
  rw [hpm] at he
  have hqm : q ^ Nat.card P ∈ K := by
    have h1 : q⁻¹ ^ Nat.card P = x⁻¹ := eq_inv_of_mul_eq_one_right he.symm
    rw [inv_pow, inv_inj] at h1
    rw [h1]
    exact hx
  have hcopq : Nat.Coprime (Nat.card P) (orderOf q) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Q hq) hcop
  have hqK : q ∈ K := (zpowers_le.mpr hqm) (mem_zpowers_pow_iff.mpr hcopq)
  refine ⟨?_, hqK⟩
  have e : p = p * q * q⁻¹ := by group
  rw [e]
  exact mul_mem hpq (inv_mem hqK)

theorem coprime_permutable_product_normalized_subgroup_intersection [Finite H]
    {P Q K : Subgroup H}
    (hcop : Nat.Coprime (Nat.card P) (Nat.card Q))
    (hPQ : (P : Set H) * (Q : Set H) = (Q : Set H) * (P : Set H))
    (hPK : P ≤ normalizer (K : Set H)) :
    ((P : Set H) * (Q : Set H)) ∩ (K : Set H) =
        ((P ⊓ K : Subgroup H) : Set H) * ((Q ⊓ K : Subgroup H) : Set H) ∧
      ((P : Set H) * (Q : Set H)) ∩ (K : Set H) =
        ((Q ⊓ K : Subgroup H) : Set H) * ((P ⊓ K : Subgroup H) : Set H) ∧
      ((P ⊓ K : Subgroup H) : Set H) * ((Q ⊓ K : Subgroup H) : Set H) =
        ((Q ⊓ K : Subgroup H) : Set H) * ((P ⊓ K : Subgroup H) : Set H) := by
  have h1 : ((P : Set H) * (Q : Set H)) ∩ (K : Set H) =
      ((P ⊓ K : Subgroup H) : Set H) * ((Q ⊓ K : Subgroup H) : Set H) := by
    ext d
    constructor
    · rintro ⟨⟨p, hp, q, hq, rfl⟩, hd⟩
      obtain ⟨hpK, hqK⟩ := mem_of_mul_mem_of_coprime hcop hPK hp hq hd
      exact ⟨p, ⟨hp, hpK⟩, q, ⟨hq, hqK⟩, rfl⟩
    · rintro ⟨p, hp, q, hq, rfl⟩
      exact ⟨⟨p, hp.1, q, hq.1, rfl⟩, mul_mem hp.2 hq.2⟩
  have h2 : ((P : Set H) * (Q : Set H)) ∩ (K : Set H) =
      ((Q ⊓ K : Subgroup H) : Set H) * ((P ⊓ K : Subgroup H) : Set H) := by
    ext d
    constructor
    · rintro ⟨hdPQ, hd⟩
      rw [hPQ] at hdPQ
      obtain ⟨q, hq, p, hp, rfl⟩ := hdPQ
      have hinv : p⁻¹ * q⁻¹ ∈ K := by
        rw [← mul_inv_rev]
        exact inv_mem hd
      obtain ⟨hpK, hqK⟩ := mem_of_mul_mem_of_coprime hcop hPK (inv_mem hp) (inv_mem hq) hinv
      exact ⟨q, Subgroup.mem_inf.mpr ⟨hq, inv_mem_iff.mp hqK⟩, p,
        Subgroup.mem_inf.mpr ⟨hp, inv_mem_iff.mp hpK⟩, rfl⟩
    · rintro ⟨q, hq, p, hp, rfl⟩
      refine ⟨?_, mul_mem hq.2 hp.2⟩
      rw [hPQ]
      exact ⟨q, hq.1, p, hp.1, rfl⟩
  exact ⟨h1, h2, h1.symm.trans h2⟩

end CFSG.Quasithin.SteinbergCD
