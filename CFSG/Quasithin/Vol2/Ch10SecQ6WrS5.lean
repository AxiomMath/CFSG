module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def pv (σ : Perm (Fin 5)) (u : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 := fun i => u (σ⁻¹ i)

theorem pv_one (u : Fin 5 → ZMod 2) : pv 1 u = u := rfl

theorem pv_mul (σ τ : Perm (Fin 5)) (u : Fin 5 → ZMod 2) : pv (σ * τ) u = pv σ (pv τ u) := by
  funext i
  simp [pv, mul_inv_rev, Perm.mul_apply]

theorem pv_add (σ : Perm (Fin 5)) (u v : Fin 5 → ZMod 2) : pv σ (u + v) = pv σ u + pv σ v := rfl

theorem pv_zero (σ : Perm (Fin 5)) : pv σ 0 = 0 := rfl

@[expose] def IsO (u : Fin 5 → ZMod 2) : Prop := ∑ i, u i = 0

instance : DecidablePred IsO := fun u => inferInstanceAs (Decidable (∑ i, u i = 0))

theorem isO_pv (σ : Perm (Fin 5)) (u : Fin 5 → ZMod 2) : IsO (pv σ u) ↔ IsO u := by
  unfold IsO pv
  rw [Equiv.sum_comp σ⁻¹ u]

theorem isO_add {u v : Fin 5 → ZMod 2} (hu : IsO u) (hv : IsO v) : IsO (u + v) := by
  unfold IsO at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hu, hv, add_zero]

@[expose] def piD8 : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def D8 : Subgroup (Perm (Fin 5)) where
  carrier := {σ | piD8 * σ = σ * piD8}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc piD8 * a⁻¹ = a⁻¹ * (a * piD8) * a⁻¹ := by group
      _ = a⁻¹ * (piD8 * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * piD8 := by group

theorem mem_D8 {σ : Perm (Fin 5)} : σ ∈ D8 ↔ piD8 * σ = σ * piD8 := Iff.rfl

instance : DecidablePred (· ∈ D8) := fun _ => decidable_of_iff _ mem_D8.symm

theorem card_D8 : Nat.card D8 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def S4 : Subgroup (Perm (Fin 5)) where
  carrier := {σ | σ 4 = 4}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Perm.mul_apply] at *
    rw [hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Perm.inv_eq_iff_eq, ha]

theorem mem_S4 {σ : Perm (Fin 5)} : σ ∈ S4 ↔ σ 4 = 4 := Iff.rfl

instance : DecidablePred (· ∈ S4) := fun _ => decidable_of_iff _ mem_S4.symm

theorem card_S4 : Nat.card S4 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
theorem exists_D8_apply : ∀ a b : Fin 5, a ≠ 4 → b ≠ 4 → ∃ σ ∈ D8, σ a = b := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_comm_not_mem : ∀ x : Perm (Fin 5), x ∉ D8 → ∃ d ∈ D8, d * x * d⁻¹ * x⁻¹ ∉ D8 := by
  decide +kernel

theorem D8_not_comm : ∃ a ∈ D8, ∃ b ∈ D8, a * b ≠ b * a :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3, by decide, swap 0 2, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem exists_not_fix_one : ∀ a : Perm (Fin 5), a * a = 1 → a ≠ 1 →
    ∃ u : Fin 5 → ZMod 2, IsO u ∧ pv a u ≠ u := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
theorem exists_fix_not_fix_two : ∀ a b : Perm (Fin 5), a * a = 1 → b * b = 1 → a * b = b * a →
    a ≠ b → a ≠ 1 → b ≠ 1 →
    (∃ u : Fin 5 → ZMod 2, IsO u ∧ pv a u = u ∧ pv b u ≠ u) ∨
      (∃ u : Fin 5 → ZMod 2, IsO u ∧ pv b u = u ∧ pv a u ≠ u) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
theorem exists_fix_ne_zero_two : ∀ a b : Perm (Fin 5), a * a = 1 → b * b = 1 → a * b = b * a →
    ∃ u : Fin 5 → ZMod 2, IsO u ∧ u ≠ 0 ∧ pv a u = u ∧ pv b u = u := by
  decide +kernel

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
