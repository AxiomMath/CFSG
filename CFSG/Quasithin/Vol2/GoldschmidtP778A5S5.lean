module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv Equiv.Perm

@[expose] def sA : Perm (Fin 5) := swap 0 1
@[expose] def sB : Perm (Fin 5) := swap 2 3
@[expose] def c3 : Perm (Fin 5) := swap 2 3 * swap 3 4

@[expose] def z01list : List (Perm (Fin 5)) := [1, sA]
@[expose] def r1list : List (Perm (Fin 5)) := [1, sA, c3, c3 ^ 2, sA * c3, sA * c3 ^ 2]
@[expose] def c1list : List (Perm (Fin 5)) :=
  r1list ++ [sB, swap 2 4, swap 3 4, sA * sB, sA * swap 2 4, sA * swap 3 4]
@[expose] def volist : List (Perm (Fin 5)) := [1, sA, sB, sA * sB]

@[expose] def listSubgroup (l : List (Perm (Fin 5))) (h1 : (1 : Perm (Fin 5)) ∈ l)
    (hm : ∀ x ∈ l, ∀ y ∈ l, x * y ∈ l) (hi : ∀ x ∈ l, x⁻¹ ∈ l) : Subgroup (Perm (Fin 5)) where
  carrier := {x | x ∈ l}
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

theorem mem_listSubgroup {l h1 hm hi} {x : Perm (Fin 5)} : x ∈ listSubgroup l h1 hm hi ↔ x ∈ l :=
  Iff.rfl

theorem card_listSubgroup {l : List (Perm (Fin 5))} {h1 hm hi} (hnd : l.Nodup) :
    Nat.card ↥(listSubgroup l h1 hm hi) = l.length := by
  have : ((listSubgroup l h1 hm hi : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))) =
      ↑(l.toFinset) := by
    ext x; simp [mem_listSubgroup]
  rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

set_option maxRecDepth 100000 in
theorem c1list_iff : ∀ g : Perm (Fin 5), sA * g = g * sA ↔ g ∈ c1list := by
  unfold c1list r1list sA sB c3; decide +kernel

theorem z01_mul : ∀ x ∈ z01list, ∀ y ∈ z01list, x * y ∈ z01list := by
  unfold z01list sA; decide +kernel
theorem z01_inv : ∀ x ∈ z01list, x⁻¹ ∈ z01list := by
  unfold z01list sA; decide +kernel
theorem r1_mul : ∀ x ∈ r1list, ∀ y ∈ r1list, x * y ∈ r1list := by
  unfold r1list sA c3; decide +kernel
theorem r1_inv : ∀ x ∈ r1list, x⁻¹ ∈ r1list := by
  unfold r1list sA c3; decide +kernel
theorem c1_mul : ∀ x ∈ c1list, ∀ y ∈ c1list, x * y ∈ c1list := by
  unfold c1list r1list sA sB c3; decide +kernel
theorem c1_inv : ∀ x ∈ c1list, x⁻¹ ∈ c1list := by
  unfold c1list r1list sA sB c3; decide +kernel
theorem vo_mul : ∀ x ∈ volist, ∀ y ∈ volist, x * y ∈ volist := by
  unfold volist sA sB; decide +kernel
theorem vo_inv : ∀ x ∈ volist, x⁻¹ ∈ volist := by
  unfold volist sA sB; decide +kernel

theorem one_mem_z01 : (1 : Perm (Fin 5)) ∈ z01list := by simp [z01list]
theorem one_mem_r1 : (1 : Perm (Fin 5)) ∈ r1list := by simp [r1list]
theorem one_mem_c1 : (1 : Perm (Fin 5)) ∈ c1list := by simp [c1list, r1list]
theorem one_mem_vo : (1 : Perm (Fin 5)) ∈ volist := by simp [volist]

@[expose] def Z01 : Subgroup (Perm (Fin 5)) := listSubgroup z01list one_mem_z01 z01_mul z01_inv
@[expose] def R1 : Subgroup (Perm (Fin 5)) := listSubgroup r1list one_mem_r1 r1_mul r1_inv
@[expose] def C1 : Subgroup (Perm (Fin 5)) := listSubgroup c1list one_mem_c1 c1_mul c1_inv
@[expose] def Vo : Subgroup (Perm (Fin 5)) := listSubgroup volist one_mem_vo vo_mul vo_inv

theorem card_Z01 : Nat.card ↥Z01 = 2 := by
  exact (card_listSubgroup (by unfold z01list sA; decide +kernel)).trans rfl

theorem card_Vo : Nat.card ↥Vo = 4 := by
  exact (card_listSubgroup (by unfold volist sA sB; decide +kernel)).trans rfl

theorem card_C1 : Nat.card ↥C1 = 12 := by
  exact (card_listSubgroup (by unfold c1list r1list sA sB c3; decide +kernel)).trans rfl

theorem r1_le_c1 : ∀ x ∈ r1list, x ∈ c1list := by
  unfold c1list; intro x hx; exact List.mem_append_left _ hx

theorem z01_le_r1 : ∀ x ∈ z01list, x ∈ r1list := by
  unfold z01list r1list; decide +kernel

theorem z01_le_vo : ∀ x ∈ z01list, x ∈ volist := by
  unfold z01list volist; decide +kernel

theorem vo_le_c1 : ∀ x ∈ volist, x ∈ c1list := by
  unfold volist c1list r1list sA sB c3; decide +kernel

theorem r1_normal : ∀ g ∈ c1list, ∀ r ∈ r1list, g * r * g⁻¹ ∈ r1list := by
  unfold c1list r1list sA sB c3; decide +kernel

theorem c1_sq : ∀ g ∈ c1list, g ^ 2 ∈ r1list := by
  unfold c1list r1list sA sB c3; decide +kernel

theorem r1_cube : ∀ r ∈ r1list, r ^ 3 ∈ z01list := by
  unfold r1list z01list sA c3; decide +kernel

theorem o2_c1 : ∀ z ∈ c1list, (∀ w ∈ c1list, (z * (w * z * w⁻¹)) ^ 4 = 1) → z ∈ z01list := by
  unfold c1list r1list z01list sA sB c3; decide +kernel

theorem r1_comm : ∀ r ∈ r1list, r * (r * sB * r⁻¹ * sB⁻¹) ∈ z01list := by
  unfold r1list z01list sA sB c3; decide +kernel

theorem z01_normal : ∀ g ∈ c1list, ∀ z ∈ z01list, g * z * g⁻¹ ∈ z01list := by
  unfold c1list r1list z01list sA sB c3; decide +kernel

theorem z01_sq : ∀ z ∈ z01list, z ^ 2 = 1 := by unfold z01list sA; decide +kernel

theorem sign_sA : Perm.sign sA = -1 := by unfold sA; decide
theorem sign_c3 : Perm.sign c3 = 1 := by unfold c3; decide
theorem c3_mem_r1 : c3 ∈ r1list := by simp [r1list]

theorem pow_four_of_two_power : ∀ x : Perm (Fin 5), x ^ 8 = 1 → x ^ 4 = 1 := by decide +kernel

theorem pow_four_of_exists_two_power (x : Perm (Fin 5)) (h : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hc : Fintype.card (Perm (Fin 5)) = 120 := by
    simp [Fintype.card_perm, Nat.factorial]
  have h2 : orderOf x ∣ 120 := by
    have := orderOf_dvd_card (G := Perm (Fin 5)) (x := x)
    rwa [hc] at this
  obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj3 : j ≤ 3 := by
    by_contra hj4
    have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [hjx] at h2
    have := h16.trans h2
    omega
  have h3 : orderOf x ∣ 8 := by
    rw [hjx]
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact pow_four_of_two_power x (orderOf_dvd_iff_pow_eq_one.mp h3)

theorem card_eq_four_of_two_power {n k : ℕ} (hk : n = 2 ^ k) (hn : 2 < n) (hd : n ∣ 60 ∨ n ∣ 12) :
    n = 4 := by
  have hk2 : k ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [← hk] at h8
    rcases hd with hd | hd
    · have := h8.trans hd; omega
    · have := h8.trans hd; omega
  interval_cases k <;> simp_all

end CFSG.Quasithin.E1.ThinA5
