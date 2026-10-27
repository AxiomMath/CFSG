module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Quasithin.SteinbergBN

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem isAlt_apply_comm (hβ : β.IsAlt) (x y : V) : β x y = β y x := by
  rw [← LinearMap.IsAlt.neg hβ x y, ZMod.neg_eq_self_mod_two]

theorem zmod_two_eq_of_iff {x y : ZMod 2} (h : x = 1 ↔ y = 1) : x = y := by
  revert x y
  decide

theorem zmod_two_eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  revert x
  decide

theorem zmod_two_add_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def transvLin (β : LinearMap.BilinForm (ZMod 2) V) (u : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (β u).smulRight u

@[simp]
theorem transvLin_apply (u x : V) : transvLin β u x = x + β u x • u := rfl

theorem transvLin_transvLin (hβ : β.IsAlt) (u x : V) :
    transvLin β u (transvLin β u x) = x := by
  rw [transvLin_apply, transvLin_apply, map_add, map_smul, hβ.self_eq_zero, smul_zero, add_zero,
    add_assoc, zmod_two_add_self, add_zero]

@[expose] def transv (hβ : β.IsAlt) (u : V) : LinearMap.GeneralLinearGroup (ZMod 2) V where
  val := transvLin β u
  inv := transvLin β u
  val_inv := LinearMap.ext fun x => transvLin_transvLin hβ u x
  inv_val := LinearMap.ext fun x => transvLin_transvLin hβ u x

variable (hβ : β.IsAlt)

@[simp]
theorem transv_apply (u x : V) :
    (transv hβ u : V →ₗ[ZMod 2] V) x = x + β u x • u := rfl

theorem transv_mul_self (u : V) : transv hβ u * transv hβ u = 1 :=
  Units.ext (LinearMap.ext fun x => transvLin_transvLin hβ u x)

theorem transv_inv (u : V) : (transv hβ u)⁻¹ = transv hβ u :=
  inv_eq_of_mul_eq_one_right (transv_mul_self hβ u)

theorem transv_zero : transv hβ (0 : V) = 1 :=
  Units.ext (LinearMap.ext fun x => by simp)

theorem transv_apply_of_orth {u x : V} (h : β u x = 0) :
    (transv hβ u : V →ₗ[ZMod 2] V) x = x := by
  simp [h]

theorem transv_apply_self (u : V) : (transv hβ u : V →ₗ[ZMod 2] V) u = u :=
  transv_apply_of_orth hβ (hβ.self_eq_zero u)

theorem transv_isometry (u x y : V) :
    β ((transv hβ u : V →ₗ[ZMod 2] V) x) ((transv hβ u : V →ₗ[ZMod 2] V) y) = β x y := by
  simp only [transv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hβ.self_eq_zero, smul_eq_mul, mul_zero, add_zero]
  rw [isAlt_apply_comm hβ x u, mul_comm (β u x) (β u y), add_assoc, zmod_two_add_self, add_zero]

theorem gl_apply_inv_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : V) :
    (g : V →ₗ[ZMod 2] V) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

theorem gl_inv_apply_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : V) :
    (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((g : V →ₗ[ZMod 2] V) x)) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem conj_transv {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : ∀ x y, β ((g : V →ₗ[ZMod 2] V) x) ((g : V →ₗ[ZMod 2] V) y) = β x y) (u : V) :
    g * transv hβ u * g⁻¹ = transv hβ ((g : V →ₗ[ZMod 2] V) u) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  have hx := gl_apply_inv_apply g x
  change (g : V →ₗ[ZMod 2] V) ((transvLin β u) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) x)) = transvLin β ((g : V →ₗ[ZMod 2] V) u) x
  rw [transvLin_apply, transvLin_apply, map_add, map_smul, hx]
  congr 2
  conv_rhs => rw [← hx]
  rw [hg]

@[expose] def isometryGroup (β : LinearMap.BilinForm (ZMod 2) V) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) where
  carrier := {g | ∀ x y, β ((g : V →ₗ[ZMod 2] V) x) ((g : V →ₗ[ZMod 2] V) y) = β x y}
  mul_mem' {g h} hg hh x y := by
    change β ((g : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) x))
      ((g : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) y)) = β x y
    rw [hg, hh]
  one_mem' _ _ := rfl
  inv_mem' {g} hg x y := by
    rw [← hg, gl_apply_inv_apply, gl_apply_inv_apply]

theorem mem_isometryGroup {g : LinearMap.GeneralLinearGroup (ZMod 2) V} :
    g ∈ isometryGroup β ↔
      ∀ x y, β ((g : V →ₗ[ZMod 2] V) x) ((g : V →ₗ[ZMod 2] V) y) = β x y :=
  Iff.rfl

theorem transv_mem_isometryGroup (u : V) : transv hβ u ∈ isometryGroup β :=
  transv_isometry hβ u

theorem closure_transv_le_isometryGroup (S : Set V) :
    Subgroup.closure (transv hβ '' S) ≤ isometryGroup β :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨u, -, rfl⟩
    exact transv_mem_isometryGroup hβ u)

variable {I : Type*}

@[expose] def pairGraph (a : I → V) : SimpleGraph I where
  Adj i j := β (a i) (a j) = 1
  symm := ⟨fun i j h => by
    rw [isAlt_apply_comm hβ]
    exact h⟩
  loopless := ⟨fun i h => by
    change β (a i) (a i) = 1 at h
    rw [hβ.self_eq_zero] at h
    exact zero_ne_one h⟩

@[simp]
theorem pairGraph_adj (a : I → V) {i j : I} : (pairGraph hβ a).Adj i j ↔ β (a i) (a j) = 1 :=
  Iff.rfl

instance (a : I → V) : DecidableRel (pairGraph hβ a).Adj :=
  fun i j => inferInstanceAs (Decidable (β (a i) (a j) = 1))

theorem pairGraph_not_adj (a : I → V) {i j : I} :
    ¬ (pairGraph hβ a).Adj i j ↔ β (a i) (a j) = 0 := by
  rw [pairGraph_adj]
  exact ⟨zmod_two_eq_zero_of_ne_one, fun h h' => zero_ne_one (h.symm.trans h')⟩

@[expose] def e6Tree : SimpleGraph (Fin 6) where
  Adj x y := s(x, y) ∈ ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(2, 5)} : Finset (Sym2 (Fin 6)))
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel e6Tree.Adj := fun x y =>
  inferInstanceAs (Decidable (s(x, y) ∈
    ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(2, 5)} : Finset (Sym2 (Fin 6)))))

theorem e6Tree_adj_iff (x y : Fin 6) :
    e6Tree.Adj x y ↔ ((x : ℕ) < 5 ∧ (y : ℕ) < 5 ∧ ((x : ℕ) + 1 = y ∨ (y : ℕ) + 1 = x)) ∨
      ((x : ℕ) = 5 ∧ (y : ℕ) = 2) ∨ ((x : ℕ) = 2 ∧ (y : ℕ) = 5) := by
  revert x y
  decide

end CFSG.Quasithin.SteinbergBN
