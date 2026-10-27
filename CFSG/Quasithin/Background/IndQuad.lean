module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.Quasithin.IndQuad

variable {Γ M : Type*} [Group Γ] [CommGroup M]

@[expose] def QuadOn (φ : Γ →* MulAut M) (E : Set Γ) : Prop :=
  ∀ h : Γ, ∀ a ∈ E, ∀ a' ∈ E, ∀ v : M,
    φ (h * a * h⁻¹) (φ (h * a' * h⁻¹) v * v⁻¹) = φ (h * a' * h⁻¹) v * v⁻¹

variable {φ : Γ →* MulAut M}

theorem fix_of_comm {E : Set Γ} (hq : QuadOn φ E) {h a a' : Γ} (ha : a ∈ E) (ha' : a' ∈ E)
    {v w : M} (hvw : φ (h * a' * h⁻¹) v * v⁻¹ = w) : φ (h * a * h⁻¹) w = w := by
  rw [← hvw]
  exact hq h a ha a' ha' v

@[expose] def fixer (φ : Γ →* MulAut M) (w : M) : Subgroup Γ where
  carrier := {g | φ g w = w}
  mul_mem' {a b} ha hb := by
    change φ (a * b) w = w
    change φ a w = w at ha
    change φ b w = w at hb
    rw [map_mul, MulAut.mul_apply, hb, ha]
  one_mem' := by
    change φ 1 w = w
    rw [map_one, MulAut.one_apply]
  inv_mem' {a} ha := by
    change φ a w = w at ha
    change φ a⁻¹ w = w
    conv_lhs => rw [← ha]
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

@[expose] def commHom (t : MulAut M) : M →* M where
  toFun v := t v * v⁻¹
  map_one' := by rw [map_one, inv_one, mul_one]
  map_mul' a b := by
    rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm]

theorem comm_mem_of_closure {X : Set M} (hX : Subgroup.closure X = ⊤) (t : MulAut M)
    {R : Subgroup M} (h : ∀ x ∈ X, t x * x⁻¹ ∈ R) (v : M) : t v * v⁻¹ ∈ R := by
  have hle : Subgroup.closure X ≤ Subgroup.comap (commHom t) R :=
    (Subgroup.closure_le _).2 fun x hx => h x hx
  rw [hX] at hle
  exact hle (Subgroup.mem_top v)

end CFSG.Quasithin.IndQuad
