module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.ASVolI.AppH

theorem not_isPGroup_two_alt {P : Type*} [Fintype P] [DecidableEq P]
    (h3 : 3 ≤ Fintype.card P) : ¬ IsPGroup 2 ↥(alternatingGroup P) := by
  intro h
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp (by omega : 2 < Fintype.card P)
  have h3c : Equiv.Perm.IsThreeCycle (Equiv.swap a b * Equiv.swap a c) :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hσ : Equiv.swap a b * Equiv.swap a c ∈ alternatingGroup P := h3c.mem_alternatingGroup
  obtain ⟨k, hk⟩ := h ⟨_, hσ⟩
  have hk' : (Equiv.swap a b * Equiv.swap a c) ^ (2 ^ k) = 1 := by
    have := congrArg (fun x : ↥(alternatingGroup P) => (x : Equiv.Perm P)) hk
    simpa using this
  have h1 : orderOf (Equiv.swap a b * Equiv.swap a c) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  rw [h3c.orderOf] at h1
  have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

theorem eq_bot_of_normal_isPGroup_alt {P : Type*} [Fintype P] [DecidableEq P]
    (h5 : 5 ≤ Fintype.card P) {M : Subgroup ↥(alternatingGroup P)} (hM : M.Normal)
    (h2 : IsPGroup 2 ↥M) : M = ⊥ := by
  haveI := hM
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := P)
    (by rw [Nat.card_eq_fintype_card]; exact h5) (N := M) with h | h
  · exact h
  · exfalso
    apply not_isPGroup_two_alt (P := P) (by omega : 3 ≤ Fintype.card P)
    intro x
    obtain ⟨k, hk⟩ := h2 ⟨x, by rw [h]; trivial⟩
    exact ⟨k, congrArg Subtype.val hk⟩

end CFSG.ASVolI.AppH
