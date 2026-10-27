module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.StandardType

namespace SUFacts

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def radB (x y : Fin 4 → F) : F :=
  ∑ k, σ (x (Fin.rev k)) * y k

theorem radB_add_left (x x' y : Fin 4 → F) : radB σ (x + x') y = radB σ x y + radB σ x' y := by
  simp only [radB, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem radB_add_right (x y y' : Fin 4 → F) : radB σ x (y + y') = radB σ x y + radB σ x y' := by
  simp only [radB, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem exists_radB_eq {x : Fin 4 → F} (hx : x ≠ 0) (c : F) : ∃ y, radB σ x y = c := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have ha : σ (x (Fin.rev (Fin.rev j))) ≠ 0 := by
    rw [Fin.rev_rev]
    exact (map_ne_zero σ).mpr hj
  refine ⟨Pi.single (Fin.rev j) ((σ (x (Fin.rev (Fin.rev j))))⁻¹ * c), ?_⟩
  rw [radB, Finset.sum_eq_single (Fin.rev j)]
  · rw [Pi.single_eq_same, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · simp

variable [Finite F] [CharP F 2]

theorem card_sq_le_of_radB_fixed {θ : F} (hθ : σ θ ≠ θ) {W : AddSubgroup (Fin 4 → F)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, σ (radB σ x y) = radB σ x y) :
    Nat.card W ^ 2 ≤ Nat.card F ^ 4 := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have : Fintype F := Fintype.ofFinite F
  set P : AddSubgroup F :=
    { carrier := {c | σ c = c}
      add_mem' := fun {a b} ha hb => by
        change σ (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := map_zero σ
      neg_mem' := fun {a} ha => by
        change σ (-a) = -a
        rw [map_neg, ha] } with hP
  set P' : Submodule (ZMod 2) F := AddSubgroup.toZModSubmodule 2 P with hP'
  have hPtop : P' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hθ ?_
    have : θ ∈ P' := by rw [htop]; exact Submodule.mem_top
    exact this
  obtain ⟨ℓ, hℓ0, hℓP⟩ := Submodule.exists_le_ker_of_lt_top P' hPtop
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, ℓ c₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ0 (LinearMap.ext h)
  let Sin : (Fin 4 → F) → (Fin 4 → F) →ₗ[ZMod 2] ZMod 2 := fun x =>
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun y => ℓ (radB σ x y)
        map_zero' := by simp [radB]
        map_add' := fun y y' => by rw [radB_add_right, map_add] }
  let S : LinearMap.BilinForm (ZMod 2) (Fin 4 → F) :=
    AddMonoidHom.toZModLinearMap 2
      { toFun := Sin
        map_zero' := LinearMap.ext fun y => by simp [Sin, radB]
        map_add' := fun x x' => LinearMap.ext fun y => by
          simp only [Sin, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_mk,
            ZeroHom.coe_mk, LinearMap.add_apply, radB_add_left, map_add] }
  have hS : ∀ x y, S x y = ℓ (radB σ x y) := fun _ _ => rfl
  have hnd : S.Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
    by_contra hx0
    obtain ⟨y, hy⟩ := exists_radB_eq σ hx0 c₀
    exact hc₀ (by rw [← hy, ← hS]; exact hx y)
  set W' : Submodule (ZMod 2) (Fin 4 → F) := AddSubgroup.toZModSubmodule 2 W with hW'
  have hle : W' ≤ S.orthogonal W' := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [hS]
    exact hℓP (hW x hx y hy)
  have hfin := LinearMap.BilinForm.finrank_orthogonal hnd W'
  have h1 : Module.finrank (ZMod 2) W' ≤ Module.finrank (ZMod 2) (S.orthogonal W') :=
    Submodule.finrank_mono hle
  have : Module.Finite (ZMod 2) (Fin 4 → F) := Module.Finite.of_finite
  have hcardV : Nat.card (Fin 4 → F) = 2 ^ Module.finrank (ZMod 2) (Fin 4 → F) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 4 → F), Nat.card_zmod]
  have hcardW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W' := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W')
    rw [Nat.card_zmod] at h
    exact h
  have hV : Nat.card (Fin 4 → F) = Nat.card F ^ 4 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  rw [hcardW, ← hV, hcardV, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end SUFacts

end CFSG.StandardType
