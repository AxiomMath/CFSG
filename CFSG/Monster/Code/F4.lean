module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Monster.Code

structure F4 where
  re : ZMod 2
  im : ZMod 2

namespace F4

@[ext] theorem ext' {x y : F4} (h₁ : x.re = y.re) (h₂ : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

theorem ext_iff' {x y : F4} : x = y ↔ x.re = y.re ∧ x.im = y.im :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext' h.1 h.2⟩

instance : DecidableEq F4 := fun _ _ => decidable_of_iff _ ext_iff'.symm

private theorem ZMod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

instance : Fintype F4 where
  elems := ⟨↑[(⟨0, 0⟩ : F4), ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], by decide⟩
  complete := by
    rintro ⟨a, b⟩
    rcases ZMod2_cases a with rfl | rfl <;> rcases ZMod2_cases b with rfl | rfl <;> decide

instance : Zero F4 := ⟨⟨0, 0⟩⟩
instance : One F4 := ⟨⟨1, 0⟩⟩
instance : Add F4 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg F4 := ⟨id⟩
instance : Sub F4 := ⟨fun x y => x + y⟩
instance : Mul F4 := ⟨fun x y => ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩⟩
instance : Inv F4 := ⟨fun x => x * x⟩
instance : Div F4 := ⟨fun x y => x * (y * y)⟩

theorem zero_def : (0 : F4) = ⟨0, 0⟩ := rfl
theorem one_def : (1 : F4) = ⟨1, 0⟩ := rfl
theorem add_def (x y : F4) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl
theorem mul_def (x y : F4) :
    x * y = ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩ := rfl

instance : CommRing F4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  neg_add_cancel := by decide
  mul_comm := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

instance : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  div_eq_mul_inv := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[expose] def α : F4 := ⟨0, 1⟩

@[expose] def ᾱ : F4 := ⟨1, 1⟩

theorem α_sq : α ^ 2 = α + 1 := by decide

theorem α_mul_α : α * α = α + 1 := by decide

theorem ᾱ_eq : ᾱ = α + 1 := by decide

theorem α_mul_ᾱ : α * ᾱ = 1 := by decide

theorem ᾱ_mul_ᾱ : ᾱ * ᾱ = α := by decide

theorem two_eq_zero : (2 : F4) = 0 := by decide

theorem card : Fintype.card F4 = 4 := by decide

theorem mem_cases (x : F4) : x = 0 ∨ x = 1 ∨ x = α ∨ x = ᾱ := by
  revert x; decide

instance : CharP F4 2 := by
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  exact two_eq_zero

@[expose] def ofF2 : ZMod 2 →+* F4 where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' := by decide
  map_zero' := rfl
  map_add' := by decide

instance : Algebra (ZMod 2) F4 := ofF2.toAlgebra

theorem algebraMap_apply (a : ZMod 2) : algebraMap (ZMod 2) F4 a = ⟨a, 0⟩ := rfl

theorem smul_def (a : ZMod 2) (x : F4) : a • x = ⟨a, 0⟩ * x := rfl

theorem eq_re_add_im (x : F4) :
    x = algebraMap (ZMod 2) F4 x.re + algebraMap (ZMod 2) F4 x.im * α := by
  revert x; decide

end F4

end CFSG.Monster.Code
