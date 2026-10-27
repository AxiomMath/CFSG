module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A5Mod

open Equiv

@[expose] def act5 (σ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  fun i => x (σ⁻¹ i)

@[expose] def ev5 : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun x => ∑ i, x i = 0

@[expose] def invs5 : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun p => p * p = 1

@[expose] def alt5 : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun p => Perm.sign p = 1

@[expose] def u5 : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

theorem act5_mul (σ τ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) :
    act5 (σ * τ) x = act5 σ (act5 τ x) := by
  funext i
  simp [act5, mul_inv_rev]

theorem act5_one (x : Fin 5 → ZMod 2) : act5 1 x = x := by
  funext i
  simp [act5]

theorem act5_add (σ : Perm (Fin 5)) (x y : Fin 5 → ZMod 2) :
    act5 σ (x + y) = act5 σ x + act5 σ y := by
  funext i
  simp [act5]

theorem act5_zero (σ : Perm (Fin 5)) : act5 σ 0 = 0 := by
  funext i
  simp [act5]

theorem mem_ev5 {x : Fin 5 → ZMod 2} : x ∈ ev5 ↔ ∑ i, x i = 0 := by
  simp [ev5]

theorem act5_mem (σ : Perm (Fin 5)) {x : Fin 5 → ZMod 2} (hx : x ∈ ev5) : act5 σ x ∈ ev5 := by
  rw [mem_ev5] at hx ⊢
  rw [← hx]
  exact Equiv.sum_comp σ⁻¹ x

theorem mem_invs5 {p : Perm (Fin 5)} : p ∈ invs5 ↔ p * p = 1 := by
  simp [invs5]

theorem mem_alt5 {p : Perm (Fin 5)} : p ∈ alt5 ↔ Perm.sign p = 1 := by
  simp [alt5]

theorem elemAbelian_le_four : ∀ p ∈ invs5, ∀ q ∈ invs5, ∀ r ∈ invs5, (p * q = q * p ∧
    p * r = r * p ∧ q * r = r * q ∧ p ≠ 1 ∧ q ≠ 1 ∧ p ≠ q) →
    (r = 1 ∨ r = p ∨ r = q ∨ r = p * q) := by
  decide +kernel

theorem exists_fix_not_fix : ∀ p ∈ invs5, ∀ q ∈ invs5, (p ≠ 1 ∧ q ≠ 1 ∧ p ≠ q ∧
    p * q = q * p) → ∃ r ∈ [p, q, p * q], ∃ x ∈ ev5, act5 r x = x ∧
      (act5 p x ≠ x ∨ act5 q x ≠ x) := by
  decide +kernel

theorem exists_fix_of_involution : ∀ g ∈ invs5, g ≠ 1 → ∃ x ∈ ev5, x ≠ 0 ∧ act5 g x = x := by
  decide +kernel

theorem mem_orbit_sum : ∀ x ∈ ev5, x ≠ 0 → ∀ y ∈ ev5,
    ∃ g₁ ∈ alt5, ∃ g₂ ∈ alt5, y = act5 g₁ x ∨ y = act5 g₁ x + act5 g₂ x := by
  decide +kernel

theorem stab_fix : ∀ v ∈ ev5, (∀ g ∈ alt5, act5 g u5 = u5 → act5 g v = v) →
    v = 0 ∨ v = u5 := by
  decide +kernel

theorem nontrivial : ∃ g ∈ alt5, ∃ x ∈ ev5, act5 g x ≠ x := by
  decide +kernel

theorem u5_mem : u5 ∈ ev5 := by
  decide

theorem u5_ne_zero : u5 ≠ 0 := by
  decide

end CFSG.Quasithin.H13.A5Mod
