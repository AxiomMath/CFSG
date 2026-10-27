module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

@[expose] def conjSub (n : G) (Q : Subgroup G) : Subgroup G where
  carrier := {x | n⁻¹ * x * n ∈ Q}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    have e : n⁻¹ * (x * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) := by group
    show n⁻¹ * (x * y) * n ∈ Q
    rw [e]
    exact Q.mul_mem hx hy
  inv_mem' := by
    intro x hx
    have e : n⁻¹ * x⁻¹ * n = (n⁻¹ * x * n)⁻¹ := by group
    show n⁻¹ * x⁻¹ * n ∈ Q
    rw [e]
    exact Q.inv_mem hx

theorem finite_subgroups [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

theorem mem_conjSub {n : G} {Q : Subgroup G} {x : G} : x ∈ conjSub n Q ↔ n⁻¹ * x * n ∈ Q := Iff.rfl

theorem conjSub_eq_iff {a b : G} {Q : Subgroup G} :
    conjSub a Q = conjSub b Q ↔ a⁻¹ * b ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have hx := SetLike.ext_iff.mp h (b * x * b⁻¹)
    rw [mem_conjSub, mem_conjSub] at hx
    have e1 : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    have e2 : a⁻¹ * (b * x * b⁻¹) * a = a⁻¹ * b * x * (a⁻¹ * b)⁻¹ := by group
    rw [e1, e2] at hx
    exact hx.symm
  · intro h
    ext x
    rw [mem_conjSub, mem_conjSub]
    have hx := h (b⁻¹ * x * b)
    have e2 : a⁻¹ * b * (b⁻¹ * x * b) * (a⁻¹ * b)⁻¹ = a⁻¹ * x * a := by group
    rw [e2] at hx
    exact hx.symm

theorem card_mul_ncard_conj [Finite G] (N Q : Subgroup G) :
    Set.ncard {Z : Subgroup G | ∃ n ∈ N, Z = conjSub n Q} *
      Nat.card ↥(N ⊓ Subgroup.normalizer (Q : Set G)) = Nat.card ↥N := by
  classical
  set Hc : Subgroup ↥N := (N ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf N with hHc
  have hrel : ∀ a b : ↥N, (QuotientGroup.leftRel Hc) a b → conjSub (a : G) Q = conjSub (b : G) Q := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ Hc := QuotientGroup.leftRel_apply.mp hab
    rw [hHc, Subgroup.mem_subgroupOf] at h1
    exact conjSub_eq_iff.mpr (Subgroup.mem_inf.mp h1).2
  let F : ↥N ⧸ Hc → Subgroup G := Quotient.lift (fun n : ↥N => conjSub (n : G) Q) hrel
  have hFinj : Function.Injective F := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        have h1 : conjSub (a : G) Q = conjSub (b : G) Q := hxy
        have h2 : (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (Q : Set G) := conjSub_eq_iff.mp h1
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        rw [hHc, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨(a⁻¹ * b).2, h2⟩
  have hrange : Set.range F = {Z : Subgroup G | ∃ n ∈ N, Z = conjSub n Q} := by
    ext Z
    constructor
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | h a => exact ⟨a, a.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨Quotient.mk _ ⟨n, hn⟩, rfl⟩
  have h1 : Nat.card (↥N ⧸ Hc) = Set.ncard (Set.range F) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.ofInjective F hFinj)
  have h2 : Hc.index * Nat.card Hc = Nat.card ↥N := Subgroup.index_mul_card Hc
  have h3 : Nat.card Hc = Nat.card ↥(N ⊓ Subgroup.normalizer (Q : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hrange, ← h1, ← h3]
  exact h2

end CFSG.RankThree.PartOne.TAIL
