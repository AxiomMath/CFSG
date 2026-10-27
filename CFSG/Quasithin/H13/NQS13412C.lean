module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.NQS13410S
public import CFSG.Quasithin.H13.NQS13410T

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

@[expose] def l3c1 : L3.Γ := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

@[expose] def l3c2 : L3.Γ := ⟨!![0, 1, 0; 1, 1, 1; 0, 0, 1], by decide⟩

@[expose] def l3E4 : Subgroup L3.Γ := l3Stab l3e1 ⊓ l3Stab l3e2

theorem l3c_facts : InL3P2 l3c1 ∧ InL3P2 l3c2 ∧ l3c1 ^ 3 = 1 ∧ l3c2 ^ 3 = 1 ∧
    L3.act (l3c1 * l3c2 * l3c1⁻¹ * l3c2⁻¹) l3e1 = l3e1 ∧
    L3.act (l3c1 * l3c2 * l3c1⁻¹ * l3c2⁻¹) l3e2 = l3e2 ∧
    l3c1 * (l3c1 * l3c2 * l3c1⁻¹ * l3c2⁻¹) * l3c1⁻¹ * (l3c1 * l3c2 * l3c1⁻¹ * l3c2⁻¹)⁻¹ ≠ 1 := by
  decide +kernel

theorem l3E4_normal : ∀ γ : L3.Γ, InL3P2 γ → ∀ e ∈ l3Blist, L3.act e l3e2 = l3e2 →
    L3.act (γ * e * γ⁻¹) l3e1 = l3e1 ∧ L3.act (γ * e * γ⁻¹) l3e2 = l3e2 := by
  decide +kernel

theorem l3E4_le_B : ∀ e : L3.Γ, L3.act e l3e1 = l3e1 → L3.act e l3e2 = l3e2 → e ∈ l3Blist := by
  decide +kernel

theorem l3E4_sq : ∀ e ∈ l3Blist, L3.act e l3e2 = l3e2 → e * e = 1 := by decide +kernel

@[expose] def a6E4list : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5]

theorem a6E4_mul : ∀ a ∈ a6E4list, ∀ b ∈ a6E4list, a * b ∈ a6E4list := by decide +kernel

theorem a6E4_inv : ∀ a ∈ a6E4list, a⁻¹ ∈ a6E4list := by decide +kernel

@[expose] def a6E4 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ a6E4list}
  mul_mem' := fun {a b} ha hb => a6E4_mul a ha b hb
  one_mem' := by decide
  inv_mem' := fun {a} ha => a6E4_inv a ha

theorem a6E4_normal : ∀ γ ∈ a6P2list, ∀ e ∈ a6E4list, γ * e * γ⁻¹ ∈ a6E4list := by
  decide +kernel

theorem a6E4_sq : ∀ e ∈ a6E4list, e * e = 1 := by
  decide +kernel

@[expose] def a6c1 : Perm (Fin 6) := c[0, 2, 4] * c[1, 3, 5]

@[expose] def a6c2 : Perm (Fin 6) := c[0, 2, 5] * c[1, 3, 4]

theorem a6c_mem : a6c1 ∈ a6P2list ∧ a6c2 ∈ a6P2list := by decide +kernel

theorem a6c_cube : a6c1 ^ 3 = 1 ∧ a6c2 ^ 3 = 1 := by decide +kernel

theorem a6c_comm : a6c1 * a6c2 * a6c1⁻¹ * a6c2⁻¹ ∈ a6E4list := by decide +kernel

theorem a6c_nc : a6c1 * (a6c1 * a6c2 * a6c1⁻¹ * a6c2⁻¹) * a6c1⁻¹ *
    (a6c1 * a6c2 * a6c1⁻¹ * a6c2⁻¹)⁻¹ ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.H13.NQS134
