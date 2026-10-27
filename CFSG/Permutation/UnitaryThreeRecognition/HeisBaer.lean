module

public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open scoped commutatorElement

structure IsBaerGroup (H : Type*) [Group H] (p : ℕ) : Prop where
  odd : Odd p
  pow_eq_one : ∀ x : H, x ^ p = 1
  comm_mem_center : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H

section ClassTwo

variable {H : Type*} [Group H]

theorem mul_comm_of_mem_center {c : H} (hc : c ∈ Subgroup.center H) (g : H) : c * g = g * c :=
  (Subgroup.mem_center_iff.mp hc g).symm

variable (hH : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H)
include hH

theorem commutatorElement_mul_left_of_center (x y z : H) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * (z * x⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅y, z⁆ * x * (z * x⁻¹ * z⁻¹) := by rw [mul_comm_of_mem_center (hH y z) x]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅x, z⁆ * ⁅y, z⁆ := mul_comm_of_mem_center (hH y z) _

theorem commutatorElement_mul_right_of_center (x y z : H) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_center hH, mul_inv_rev,
    commutatorElement_inv, commutatorElement_inv]
  exact mul_comm_of_mem_center (hH x z) _

omit hH in
theorem commutatorElement_eq_one_of_mem_center_right {c : H} (hc : c ∈ Subgroup.center H)
    (x : H) : ⁅x, c⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_mem_center hc x).symm

omit hH in
theorem commutatorElement_eq_one_of_mem_center_left {c : H} (hc : c ∈ Subgroup.center H)
    (x : H) : ⁅c, x⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_mem_center hc x)

theorem commutatorElement_mul_center_left (x y : H) {c : H} (hc : c ∈ Subgroup.center H) :
    ⁅x * c, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_of_center hH, commutatorElement_eq_one_of_mem_center_left hc,
    mul_one]

theorem commutatorElement_mul_center_right (x y : H) {c : H} (hc : c ∈ Subgroup.center H) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_of_center hH, commutatorElement_eq_one_of_mem_center_right hc,
    mul_one]

end ClassTwo

section BaerAdd

variable {H : Type*} [Group H] {p : ℕ}

@[expose] def baerAdd (p : ℕ) (x y : H) : H := x * y * ⁅y, x⁆ ^ ((p + 1) / 2)

theorem baerAdd_one (x : H) : baerAdd p x 1 = x := by
  simp [baerAdd]

theorem one_baerAdd (x : H) : baerAdd p 1 x = x := by
  simp [baerAdd]

theorem baerAdd_pow (x : H) (n : ℕ) : baerAdd p (x ^ n) x = x ^ (n + 1) := by
  have : ⁅x, x ^ n⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (Commute.self_pow x n).eq
  simp [baerAdd, this, pow_succ]

theorem baerAdd_inv (x : H) : baerAdd p x⁻¹ x = 1 := by
  have : ⁅x, x⁻¹⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (by group)
  simp [baerAdd, this]

variable (hB : IsBaerGroup H p)
include hB

theorem baerAdd_assoc (x y z : H) :
    baerAdd p (baerAdd p x y) z = baerAdd p x (baerAdd p y z) := by
  have hH := hB.comm_mem_center
  set h := (p + 1) / 2
  have e1 : ⁅z, x * y * ⁅y, x⁆ ^ h⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
    rw [commutatorElement_mul_center_right hH _ _ (Subgroup.pow_mem _ (hH y x) _),
      commutatorElement_mul_right_of_center hH]
  have e2 : ⁅y * z * ⁅z, y⁆ ^ h, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    rw [commutatorElement_mul_center_left hH _ _ (Subgroup.pow_mem _ (hH z y) _),
      commutatorElement_mul_left_of_center hH]
  have hc : ∀ {a b : H}, a ∈ Subgroup.center H → Commute a b := fun ha =>
    mul_comm_of_mem_center ha _
  have cxy := hH y x
  have czx := hH z x
  have czy := hH z y
  simp only [baerAdd]
  rw [e1, e2, (hc czx).mul_pow, (hc cxy).mul_pow]
  have m1 : ⁅y, x⁆ ^ h * z = z * ⁅y, x⁆ ^ h := hc (Subgroup.pow_mem _ cxy _)
  calc x * y * ⁅y, x⁆ ^ h * z * (⁅z, x⁆ ^ h * ⁅z, y⁆ ^ h)
      = x * y * (⁅y, x⁆ ^ h * z) * (⁅z, x⁆ ^ h * ⁅z, y⁆ ^ h) := by group
    _ = x * y * z * (⁅y, x⁆ ^ h * (⁅z, x⁆ ^ h * ⁅z, y⁆ ^ h)) := by rw [m1]; group
    _ = x * y * z * (⁅z, y⁆ ^ h * (⁅y, x⁆ ^ h * ⁅z, x⁆ ^ h)) := by
        rw [← mul_assoc (⁅y, x⁆ ^ h), mul_comm_of_mem_center (Subgroup.pow_mem _ czy _)]
    _ = x * (y * z * ⁅z, y⁆ ^ h) * (⁅y, x⁆ ^ h * ⁅z, x⁆ ^ h) := by group

theorem two_mul_baerExp : (p + 1) / 2 + (p + 1) / 2 = p + 1 := by
  obtain ⟨k, hk⟩ := hB.odd
  omega

theorem baerAdd_comm (x y : H) : baerAdd p x y = baerAdd p y x := by
  have hH := hB.comm_mem_center
  have hsq : ⁅x, y⁆ ^ ((p + 1) / 2) * ⁅x, y⁆ ^ ((p + 1) / 2) = ⁅x, y⁆ := by
    rw [← pow_add, two_mul_baerExp hB, pow_succ, hB.pow_eq_one, one_mul]
  have key : ⁅x, y⁆ * (⁅x, y⁆ ^ ((p + 1) / 2))⁻¹ = ⁅x, y⁆ ^ ((p + 1) / 2) := by
    calc ⁅x, y⁆ * (⁅x, y⁆ ^ ((p + 1) / 2))⁻¹
        = ⁅x, y⁆ ^ ((p + 1) / 2) * ⁅x, y⁆ ^ ((p + 1) / 2) * (⁅x, y⁆ ^ ((p + 1) / 2))⁻¹ := by
          rw [hsq]
      _ = ⁅x, y⁆ ^ ((p + 1) / 2) := by group
  have hxy : x * y = ⁅x, y⁆ * (y * x) := by simp only [commutatorElement_def]; group
  simp only [baerAdd]
  rw [hxy, ← commutatorElement_inv (g₁ := x) (g₂ := y), inv_pow,
    mul_comm_of_mem_center (hH x y) (y * x), mul_assoc (y * x), key]

end BaerAdd

@[expose] def Baer (H : Type*) [Group H] (p : ℕ) (_hB : IsBaerGroup H p) : Type _ := H

namespace Baer

variable {H : Type*} [Group H] {p : ℕ} {hB : IsBaerGroup H p}

@[expose] def toB (hB : IsBaerGroup H p) (x : H) : Baer H p hB := x

@[expose] def ofB (x : Baer H p hB) : H := x

@[simp] theorem ofB_toB (x : H) : ofB (toB hB x) = x := rfl

@[simp] theorem toB_ofB (x : Baer H p hB) : toB hB (ofB x) = x := rfl

instance [Finite H] : Finite (Baer H p hB) := inferInstanceAs (Finite H)

theorem toB_injective : Function.Injective (toB hB) := fun _ _ h => h

theorem ofB_injective : Function.Injective (ofB (hB := hB)) := fun _ _ h => h

instance : AddCommGroup (Baer H p hB) where
  add x y := toB hB (baerAdd p (ofB x) (ofB y))
  zero := toB hB 1
  neg x := toB hB (ofB x)⁻¹
  nsmul n x := toB hB (ofB x ^ n)
  zsmul n x := toB hB (ofB x ^ n)
  add_assoc x y z := baerAdd_assoc hB (ofB x) (ofB y) (ofB z)
  zero_add x := one_baerAdd (ofB x)
  add_zero x := baerAdd_one (ofB x)
  nsmul_zero x := show toB hB (ofB x ^ 0) = toB hB 1 by rw [pow_zero]
  nsmul_succ n x := (baerAdd_pow (ofB x) n).symm
  zsmul_zero' x := show toB hB (ofB x ^ (0 : ℤ)) = toB hB 1 by rw [zpow_zero]
  zsmul_succ' n x := by
    change ofB x ^ ((n + 1 : ℕ) : ℤ) = baerAdd p (ofB x ^ (n : ℤ)) (ofB x)
    rw [zpow_natCast, zpow_natCast, baerAdd_pow]
  zsmul_neg' n x := by
    change ofB x ^ (Int.negSucc n) = (ofB x ^ ((n + 1 : ℕ) : ℤ))⁻¹
    rw [zpow_negSucc, zpow_natCast]
  neg_add_cancel x := baerAdd_inv (ofB x)
  add_comm x y := baerAdd_comm hB (ofB x) (ofB y)

theorem ofB_add (x y : Baer H p hB) :
    ofB (x + y) = ofB x * ofB y * ⁅ofB y, ofB x⁆ ^ ((p + 1) / 2) := rfl

@[simp] theorem ofB_zero : ofB (0 : Baer H p hB) = 1 := rfl

@[simp] theorem ofB_neg (x : Baer H p hB) : ofB (-x) = (ofB x)⁻¹ := rfl

@[simp] theorem ofB_nsmul (n : ℕ) (x : Baer H p hB) : ofB (n • x) = ofB x ^ n := rfl

@[simp] theorem toB_one : toB hB (1 : H) = 0 := rfl

@[simp] theorem toB_inv (x : H) : toB hB x⁻¹ = -toB hB x := rfl

@[simp] theorem toB_pow (x : H) (n : ℕ) : toB hB (x ^ n) = n • toB hB x := rfl

theorem toB_eq_zero {x : H} : toB hB x = 0 ↔ x = 1 := Iff.rfl

theorem eq_zero_iff_ofB_eq_one {v : Baer H p hB} : v = 0 ↔ ofB v = 1 := Iff.rfl

instance : Module (ZMod p) (Baer H p hB) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    change toB hB (ofB x ^ p) = toB hB 1
    rw [hB.pow_eq_one]

theorem toB_mul_of_mem_center (x : H) {c : H} (hc : c ∈ Subgroup.center H) :
    toB hB (x * c) = toB hB x + toB hB c := by
  apply ofB_injective
  rw [ofB_add, ofB_toB, ofB_toB, ofB_toB, commutatorElement_eq_one_of_mem_center_left hc,
    one_pow, mul_one]

theorem toB_mul (x y : H) :
    toB hB (x * y) = toB hB x + toB hB y + toB hB (⁅x, y⁆ ^ ((p + 1) / 2)) := by
  have hc : ⁅x, y⁆ ^ ((p + 1) / 2) ∈ Subgroup.center H :=
    Subgroup.pow_mem _ (hB.comm_mem_center x y) _
  apply ofB_injective
  simp only [ofB_add, ofB_toB]
  rw [commutatorElement_eq_one_of_mem_center_left hc, one_pow, mul_one,
    ← commutatorElement_inv (g₁ := x) (g₂ := y), inv_pow, inv_mul_cancel_right]

@[expose] def homOf {H' : Type*} [Group H'] {hB' : IsBaerGroup H' p} (φ : H →* H') :
    Baer H p hB →+ Baer H' p hB' where
  toFun x := toB hB' (φ (ofB x))
  map_zero' := show toB hB' (φ 1) = toB hB' 1 by rw [map_one]
  map_add' x y := by
    apply ofB_injective
    simp only [ofB_toB, ofB_add, map_mul, map_pow, map_commutatorElement]

@[simp] theorem homOf_toB {H' : Type*} [Group H'] {hB' : IsBaerGroup H' p} (φ : H →* H')
    (x : H) : homOf (hB := hB) (hB' := hB') φ (toB hB x) = toB hB' (φ x) := rfl

theorem bracket_add_right (u v v' : Baer H p hB) :
    toB hB ⁅ofB u, ofB (v + v')⁆ = toB hB ⁅ofB u, ofB v⁆ + toB hB ⁅ofB u, ofB v'⁆ := by
  have hH := hB.comm_mem_center
  rw [ofB_add, commutatorElement_mul_center_right hH _ _ (Subgroup.pow_mem _ (hH _ _) _),
    commutatorElement_mul_right_of_center hH, toB_mul_of_mem_center _ (hH _ _)]

theorem bracket_add_left (u u' v : Baer H p hB) :
    toB hB ⁅ofB (u + u'), ofB v⁆ = toB hB ⁅ofB u, ofB v⁆ + toB hB ⁅ofB u', ofB v⁆ := by
  have hH := hB.comm_mem_center
  rw [ofB_add, commutatorElement_mul_center_left hH _ _ (Subgroup.pow_mem _ (hH _ _) _),
    commutatorElement_mul_left_of_center hH, toB_mul_of_mem_center _ (hH _ _)]

@[expose] def bracket : Baer H p hB →+ Baer H p hB →+ Baer H p hB :=
  AddMonoidHom.mk'
    (fun u => AddMonoidHom.mk' (fun v => toB hB ⁅ofB u, ofB v⁆) (bracket_add_right u))
    (fun u u' => by ext v; exact bracket_add_left u u' v)

@[simp] theorem bracket_apply (u v : Baer H p hB) : bracket u v = toB hB ⁅ofB u, ofB v⁆ := rfl

@[simp] theorem bracket_self (u : Baer H p hB) : bracket u u = 0 := by
  rw [bracket_apply, commutatorElement_self]; rfl

@[expose] def toSubgroup (U : AddSubgroup (Baer H p hB)) (hU : ∀ x y : H, toB hB ⁅x, y⁆ ∈ U) :
    Subgroup H where
  carrier := {x | toB hB x ∈ U}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    rw [toB_mul, toB_pow]
    exact U.add_mem (U.add_mem hx hy) (U.nsmul_mem (hU x y) _)
  one_mem' := U.zero_mem
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, toB_inv] at *
    exact U.neg_mem hx

@[simp] theorem mem_toSubgroup (U : AddSubgroup (Baer H p hB))
    (hU : ∀ x y : H, toB hB ⁅x, y⁆ ∈ U) (x : H) : x ∈ toSubgroup U hU ↔ toB hB x ∈ U :=
  Iff.rfl

end Baer

end CFSG.UnitaryThreeRecognition.Heisenberg
