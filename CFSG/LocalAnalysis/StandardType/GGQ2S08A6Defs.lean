module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.A6

open Matrix

abbrev V6 : Type := Fin 6 → ZMod 3

@[expose] def one6 : V6 := fun _ => 1

@[expose] def e6 (i : Fin 6) : V6 := Pi.single i 1

@[expose] def perm6 (σ : Equiv.Perm (Fin 6)) : V6 ≃ₗ[ZMod 3] V6 :=
  LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) σ.symm

theorem perm6_apply (σ : Equiv.Perm (Fin 6)) (v : V6) (i : Fin 6) :
    perm6 σ v i = v (σ.symm i) :=
  rfl

@[expose] def refl6 (c a : V6) (h : a ⬝ᵥ c = 2) : V6 ≃ₗ[ZMod 3] V6 where
  toFun v := v - (a ⬝ᵥ v) • c
  invFun v := v - (a ⬝ᵥ v) • c
  map_add' v w := by
    rw [dotProduct_add, add_smul]
    abel
  map_smul' s v := by
    rw [dotProduct_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sub]
  left_inv v := by
    simp only [dotProduct_sub, dotProduct_smul, h, smul_eq_mul]
    rw [sub_sub, ← add_smul, sub_eq_self]
    have h3 : (a ⬝ᵥ v) + ((a ⬝ᵥ v) - (a ⬝ᵥ v) * 2) = 0 := by
      ring_nf
    rw [h3, zero_smul]
  right_inv v := by
    simp only [dotProduct_sub, dotProduct_smul, h, smul_eq_mul]
    rw [sub_sub, ← add_smul, sub_eq_self]
    have h3 : (a ⬝ᵥ v) + ((a ⬝ᵥ v) - (a ⬝ᵥ v) * 2) = 0 := by
      ring_nf
    rw [h3, zero_smul]

theorem refl6_apply (c a : V6) (h : a ⬝ᵥ c = 2) (v : V6) :
    refl6 c a h v = v - (a ⬝ᵥ v) • c :=
  rfl

@[expose] def IsRefl6 (g : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  ∃ c a : V6, a ⬝ᵥ c = 2 ∧ ∀ v, g v = v - (a ⬝ᵥ v) • c

@[expose] def IsTransv6 (g : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  ∃ c a : V6, c ≠ 0 ∧ a ≠ 0 ∧ a ⬝ᵥ c = 0 ∧ ∀ v, g v = v + (a ⬝ᵥ v) • c

@[expose] def FixesLine6 (g : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  g one6 = one6 ∨ g one6 = -one6

@[expose] def MovesLine6 (g : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  g one6 ≠ one6 ∧ g one6 ≠ -one6

structure A6Hyp (A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)) : Prop where
  le : M ≤ A
  perm_mem : ∀ σ, perm6 σ ∈ M
  noTransv : ∀ g ∈ A, ¬ IsTransv6 g
  normW : ∀ g ∈ A, FixesLine6 g → ∀ σ, ∃ τ, g * perm6 σ * g⁻¹ = perm6 τ
  stab_mem : ∀ g ∈ A, FixesLine6 g → g ∈ M

@[expose] def A6Mono (f : Fin 6 → V6) (g : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ i, g (f i) = ε i • f (σ i)

@[expose] def A6MonoEven (f : Fin 6 → V6) (g : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ZMod 3), (∀ i, ε i ≠ 0) ∧ (∏ i, ε i = 1) ∧
    ∀ i, g (f i) = ε i • f (σ i)

@[expose] def sign6 (i : Fin 6) : V6 ≃ₗ[ZMod 3] V6 :=
  refl6 (e6 i) (2 • e6 i) (by simp [e6, dotProduct_single])

@[expose] def rB : V6 ≃ₗ[ZMod 3] V6 := sign6 5

@[expose] def rD : V6 ≃ₗ[ZMod 3] V6 :=
  refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide)

@[expose] def rS : V6 ≃ₗ[ZMod 3] V6 :=
  refl6 (e6 5) (one6 + e6 5) (by decide)

end CFSG.StandardType.A6

end
