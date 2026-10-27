module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Equiv

theorem card_modEq_card_fix {α : Type*} [Finite α] {p : ℕ} [Fact p.Prime] (g : Perm α)
    (hg : g ^ p = 1) : Nat.card α ≡ Nat.card {x // g x = x} [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers g) := by
    by_cases h1 : g = 1
    · refine IsPGroup.of_card (n := 0) ?_
      rw [Nat.card_zpowers, h1, orderOf_one, pow_zero]
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hg h1
  have h1 := hP.card_modEq_card_fixedPoints α
  have e : MulAction.fixedPoints (Subgroup.zpowers g) α = {x | g x = x} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · rintro h ⟨m, hm⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      exact Perm.zpow_apply_eq_self_of_apply_eq_self h k
  rw [e] at h1
  exact h1

theorem apply_fix_iff {α : Type*} {k h : Perm α} (hc : Commute k h) (x : α) :
    h (k x) = k x ↔ h x = x := by
  have e : h (k x) = k (h x) := by
    have := congrArg (fun f : Perm α => f x) hc.eq
    simpa [Perm.mul_apply] using this.symm
  rw [e]
  exact k.injective.eq_iff

theorem subtypePerm_pow_eq_one {α : Type*} {k h : Perm α} (hc : Commute k h) {p : ℕ}
    (hk : k ^ p = 1) : (k.subtypePerm (p := fun x => h x = x) (apply_fix_iff hc)) ^ p = 1 := by
  ext x
  rw [Perm.subtypePerm_pow, Perm.subtypePerm_apply]
  simp [hk]

theorem exists_fix_of_not_dvd {α : Type*} [Finite α] {k h : Perm α} (hc : Commute k h) {p : ℕ}
    [Fact p.Prime] (hk : k ^ p = 1) (hd : ¬ p ∣ Nat.card {x // h x = x}) :
    ∃ x, h x = x ∧ k x = x := by
  have h1 := card_modEq_card_fix (k.subtypePerm (p := fun x => h x = x) (apply_fix_iff hc))
    (subtypePerm_pow_eq_one hc hk)
  by_contra hne
  have h0 : Nat.card {y : {x // h x = x} //
      (k.subtypePerm (p := fun x => h x = x) (apply_fix_iff hc)) y = y} = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨⟨x, hx⟩, hy⟩ => hne ⟨x, hx, ?_⟩⟩
    have := congrArg Subtype.val hy
    simpa using this
  rw [h0] at h1
  exact hd (Nat.modEq_zero_iff_dvd.mp h1)

theorem card_fix_lt {α : Type*} [Finite α] {k : Perm α} (hk : k ≠ 1) :
    Nat.card {x // k x = x} < Nat.card α := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨x, hx⟩ : ∃ x, k x ≠ x := by
    by_contra h
    exact hk (Perm.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_lt hx

theorem perm7_false {k h : Perm (Fin 7)} (hk : orderOf k = 7) (hh : orderOf h = 3)
    (hc : Commute k h) : False := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk7 : k ^ 7 = 1 := by have := pow_orderOf_eq_one k; rwa [hk] at this
  have hh3 : h ^ 3 = 1 := by have := pow_orderOf_eq_one h; rwa [hh] at this
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; omega
  have hh1 : h ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hh; omega
  have hc7 : Nat.card (Fin 7) = 7 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 7)
  have hFk := card_modEq_card_fix k hk7
  have hlt := card_fix_lt hk1
  rw [hc7] at hFk hlt
  have hFk0 : Nat.card {x // k x = x} = 0 := by
    unfold Nat.ModEq at hFk
    omega
  have hFh := card_modEq_card_fix h hh3
  have hlth := card_fix_lt hh1
  rw [hc7] at hFh hlth
  have hd : ¬ 7 ∣ Nat.card {x // h x = x} := by
    unfold Nat.ModEq at hFh
    omega
  obtain ⟨x, -, hkx⟩ := exists_fix_of_not_dvd hc hk7 hd
  have : 0 < Nat.card {x // k x = x} := Nat.card_pos_iff.mpr ⟨⟨⟨x, hkx⟩⟩, inferInstance⟩
  omega

theorem alt7_false {k h : ↥(alternatingGroup (Fin 7))} (hk : orderOf k = 7) (hh : orderOf h = 3)
    (hc : Commute k h) : False :=
  perm7_false (k := (k : Perm (Fin 7))) (h := (h : Perm (Fin 7)))
    (by rw [Subgroup.orderOf_coe]; exact hk) (by rw [Subgroup.orderOf_coe]; exact hh)
    (by rw [Commute, SemiconjBy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc.eq])

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
