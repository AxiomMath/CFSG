module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.F53

open Equiv

theorem mem_sup_of_commute {X : Type*} [Group X] {A B : Subgroup X}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have := hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
            exact this.symm }
  have : A ⊔ B ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩) (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact this hx

@[expose] def klein4 : Subgroup (Perm (Fin 4)) where
  carrier := {x | x ^ 2 = 1 ∧ Perm.sign x = 1}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +revert
  inv_mem' := by
    intro a ha
    revert a
    decide +revert

theorem mem_klein4 {x : Perm (Fin 4)} : x ∈ klein4 ↔ x ^ 2 = 1 ∧ Perm.sign x = 1 := Iff.rfl

theorem klein4_normal : klein4.Normal := by
  have h : ∀ x g : Perm (Fin 4), (x ^ 2 = 1 ∧ Perm.sign x = 1) →
      ((g * x * g⁻¹) ^ 2 = 1 ∧ Perm.sign (g * x * g⁻¹) = 1) := by decide +kernel
  exact ⟨fun x hx g => h x g hx⟩

instance : DecidablePred (· ∈ klein4) := fun _ => decidable_of_iff _ mem_klein4.symm

theorem card_klein4 : Nat.card klein4 = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem exists_not_pow_eight :
    ∀ x : Perm (Fin 4), x ∉ klein4 → ∃ g : Perm (Fin 4), (x * (g * x * g⁻¹)) ^ 8 ≠ 1 := by
  decide +kernel

theorem exists_conj_klein4 :
    ∀ x v : Perm (Fin 4), x ∈ klein4 → v ∈ klein4 → x ≠ 1 → v ≠ 1 →
      ∃ g : Perm (Fin 4), g * x * g⁻¹ = v := by
  decide +kernel

theorem pow_eight_of_two_pow {y : Perm (Fin 4)} {k : ℕ} (h : y ^ 2 ^ k = 1) : y ^ 8 = 1 := by
  have h24 : y ^ 24 = 1 := by
    have := pow_card_eq_one' (G := Perm (Fin 4)) (x := y)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have h2 : orderOf y ∣ 24 := orderOf_dvd_of_pow_eq_one h24
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj4
    have : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := this.trans h2
    omega
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow 2 hj3)

theorem normal2_le_klein4 {N : Subgroup (Perm (Fin 4))} [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ klein4 := by
  intro x hx
  by_contra hxk
  obtain ⟨g, hg⟩ := exists_not_pow_eight x hxk
  apply hg
  have hy : x * (g * x * g⁻¹) ∈ N := N.mul_mem hx (Subgroup.Normal.conj_mem ‹_› x hx g)
  obtain ⟨k, hk⟩ := hN ⟨_, hy⟩
  exact pow_eight_of_two_pow (k := k) (by simpa using congrArg Subtype.val hk)

theorem klein4_le_of_normal2 {N : Subgroup (Perm (Fin 4))} [N.Normal] (hN : IsPGroup 2 N)
    (hne : N ≠ ⊥) : klein4 ≤ N := by
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hx := x.2
  have hxk : (x : Perm (Fin 4)) ∈ klein4 := normal2_le_klein4 hN hx
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]; exact N.one_mem
  · have hx1' : (x : Perm (Fin 4)) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨g, hg⟩ := exists_conj_klein4 x v hxk hv hx1' hv1
    rw [← hg]
    exact Subgroup.Normal.conj_mem ‹_› x.1 hx g

theorem klein4_comm : ∀ w ∈ klein4, ∀ w' ∈ klein4, w * w' = w' * w := by
  decide +kernel

@[expose] def cyc4 : Perm (Fin 4) := swap 0 1 * swap 1 2

theorem cyc4_pow_three : cyc4 ^ 3 = 1 := by unfold cyc4; decide +kernel

theorem cyc4_ne_one : cyc4 ≠ 1 := by unfold cyc4; decide +kernel

theorem orderOf_cyc4 : orderOf cyc4 = 3 :=
  orderOf_eq_prime cyc4_pow_three cyc4_ne_one

theorem exists_not_sq_perm3 :
    ∀ x : Perm (Fin 3), x ≠ 1 → ∃ g : Perm (Fin 3), (x * (g * x * g⁻¹)) ^ 2 ≠ 1 := by
  decide +kernel

theorem sq_of_two_pow_perm3 {y : Perm (Fin 3)} {k : ℕ} (h : y ^ 2 ^ k = 1) : y ^ 2 = 1 := by
  have h6 : y ^ 6 = 1 := by
    have := pow_card_eq_one' (G := Perm (Fin 3)) (x := y)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have h2 : orderOf y ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  rw [hj] at h2
  have hj3 : j ≤ 1 := by
    by_contra hj4
    have : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := this.trans h2
    omega
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow 2 hj3)

theorem klein4_eq_comm_of_three :
    ∀ c : Perm (Fin 4), c ^ 3 = 1 → c ≠ 1 → ∀ v ∈ klein4, ∃ w ∈ klein4, v = w * (c * w * c⁻¹) := by
  decide +kernel

theorem centralizer_klein4 :
    ∀ t : Perm (Fin 4), (∀ v ∈ klein4, t * v = v * t) → t ∈ klein4 := by
  decide +kernel

end CFSG.Quasithin.F53
