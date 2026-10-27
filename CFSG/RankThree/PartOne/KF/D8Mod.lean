module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

abbrev D8Mod (p : ℕ) (K : Type) [Field K] : Type := rootsOfUnity p K × rootsOfUnity p K

@[expose] def d8Rot : MulAut (D8Mod p K) where
  toFun v := (v.2, v.1⁻¹)
  invFun v := (v.2⁻¹, v.1)
  left_inv v := by simp
  right_inv v := by simp
  map_mul' v w := by simp [mul_comm]

@[expose] def d8Ref : MulAut (D8Mod p K) where
  toFun v := (v.1⁻¹, v.2)
  invFun v := (v.1⁻¹, v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_mul' v w := by simp [mul_comm]

theorem d8Rot_pow_four : (d8Rot : MulAut (D8Mod p K)) ^ 4 = 1 := by
  ext v <;> simp [pow_succ, d8Rot]

theorem d8Ref_mul_self : (d8Ref : MulAut (D8Mod p K)) * d8Ref = 1 := by
  ext v <;> simp [d8Ref]

theorem d8Ref_rot_ref : (d8Ref : MulAut (D8Mod p K)) * d8Rot * d8Ref = d8Rot⁻¹ := by
  ext v <;> simp [d8Ref, d8Rot]

section Lift

variable {G : Type*} [Group G] {n : ℕ} [NeZero n] (x y : G)

@[expose] def zmodPow (i : ZMod n) : G := x ^ i.val

theorem zmodPow_add (hx : x ^ n = 1) (i j : ZMod n) :
    zmodPow x (i + j) = zmodPow x i * zmodPow x j := by
  unfold zmodPow
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]

omit [NeZero n] in
theorem zmodPow_zero : zmodPow x (0 : ZMod n) = 1 := by simp [zmodPow]

theorem zmodPow_neg (hx : x ^ n = 1) (i : ZMod n) : zmodPow x (-i) = (zmodPow x i)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← zmodPow_add x hx, neg_add_cancel, zmodPow_zero]

omit [NeZero n] in
theorem zmodPow_mul_y (hxy : y * x * y = x⁻¹) (hy : y * y = 1) (i : ZMod n) :
    zmodPow x i * y = y * (zmodPow x i)⁻¹ := by
  have hyx : y * x = x⁻¹ * y := by
    calc y * x = y * x * y * y := by rw [mul_assoc (y * x), hy, mul_one]
      _ = x⁻¹ * y := by rw [hxy]
  have key : ∀ k : ℕ, x ^ k * y = y * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * y = x ^ k * (x * y) := by rw [pow_succ, mul_assoc]
        _ = x ^ k * (y * x⁻¹) := by
          congr 1
          calc x * y = y * y * x * y := by rw [hy, one_mul]
            _ = y * (y * x * y) := by simp only [mul_assoc]
            _ = y * x⁻¹ := by rw [hxy]
        _ = (x ^ k * y) * x⁻¹ := by rw [mul_assoc]
        _ = y * (x ^ k)⁻¹ * x⁻¹ := by rw [ih]
        _ = y * (x ^ (k + 1))⁻¹ := by rw [mul_assoc, ← mul_inv_rev, ← pow_succ']
  exact key _

@[expose] def dihedralLift (hx : x ^ n = 1) (hy : y * y = 1) (hxy : y * x * y = x⁻¹) :
    DihedralGroup n →* G where
  toFun
    | .r i => zmodPow x i
    | .sr i => y * zmodPow x i
  map_one' := by
    rw [← DihedralGroup.r_zero]
    exact zmodPow_zero x
  map_mul' a b := by
    rcases a with i | i <;> rcases b with j | j
    · exact zmodPow_add x hx i j
    · show y * zmodPow x (j - i) = zmodPow x i * (y * zmodPow x j)
      calc y * zmodPow x (j - i) = y * ((zmodPow x i)⁻¹ * zmodPow x j) := by
            rw [sub_eq_add_neg, add_comm, zmodPow_add x hx, zmodPow_neg x hx]
        _ = zmodPow x i * (y * zmodPow x j) := by
            rw [← mul_assoc, ← zmodPow_mul_y x y hxy hy, mul_assoc]
    · show y * zmodPow x (i + j) = y * zmodPow x i * zmodPow x j
      rw [zmodPow_add x hx, mul_assoc]
    · show zmodPow x (j - i) = y * zmodPow x i * (y * zmodPow x j)
      calc zmodPow x (j - i) = (y * y) * ((zmodPow x i)⁻¹ * zmodPow x j) := by
            rw [hy, one_mul, sub_eq_add_neg, add_comm, zmodPow_add x hx, zmodPow_neg x hx]
        _ = y * (y * (zmodPow x i)⁻¹) * zmodPow x j := by simp only [mul_assoc]
        _ = y * (zmodPow x i * y) * zmodPow x j := by rw [zmodPow_mul_y x y hxy hy]
        _ = y * zmodPow x i * (y * zmodPow x j) := by simp only [mul_assoc]

theorem dihedralLift_r (hx : x ^ n = 1) (hy : y * y = 1) (hxy : y * x * y = x⁻¹) (i : ZMod n) :
    dihedralLift x y hx hy hxy (.r i) = x ^ i.val := rfl

theorem dihedralLift_sr (hx : x ^ n = 1) (hy : y * y = 1) (hxy : y * x * y = x⁻¹) (i : ZMod n) :
    dihedralLift x y hx hy hxy (.sr i) = y * x ^ i.val := rfl

end Lift

@[expose] def d8Act : DihedralGroup 4 →* MulAut (D8Mod p K) :=
  dihedralLift d8Rot d8Ref d8Rot_pow_four d8Ref_mul_self d8Ref_rot_ref

theorem d8Rot_apply (v : D8Mod p K) : (d8Rot : MulAut (D8Mod p K)) v = (v.2, v.1⁻¹) := rfl

theorem d8Ref_apply (v : D8Mod p K) : (d8Ref : MulAut (D8Mod p K)) v = (v.1⁻¹, v.2) := rfl

theorem d8Act_r (v : D8Mod p K) (i : ZMod 4) :
    d8Act (DihedralGroup.r i) v = (d8Rot ^ i.val) v := rfl

theorem d8Act_sr (v : D8Mod p K) (i : ZMod 4) :
    d8Act (DihedralGroup.sr i) v = (d8Ref * d8Rot ^ i.val : MulAut (D8Mod p K)) v := rfl

theorem d8Act_r_zero (v : D8Mod p K) : d8Act (DihedralGroup.r 0) v = v := by
  rw [d8Act_r]; simp

theorem d8Act_r_one (v : D8Mod p K) : d8Act (DihedralGroup.r 1) v = (v.2, v.1⁻¹) := by
  rw [d8Act_r]
  have : (1 : ZMod 4).val = 1 := by decide
  rw [this, pow_one]; rfl

theorem d8Act_r_two (v : D8Mod p K) : d8Act (DihedralGroup.r 2) v = (v.1⁻¹, v.2⁻¹) := by
  rw [d8Act_r]
  have : (2 : ZMod 4).val = 2 := by decide
  rw [this, pow_two]; rfl

theorem d8Act_r_three (v : D8Mod p K) : d8Act (DihedralGroup.r 3) v = (v.2⁻¹, v.1) := by
  rw [d8Act_r]
  have : (3 : ZMod 4).val = 3 := by decide
  rw [this, pow_succ, pow_two]
  show d8Rot (d8Rot (d8Rot v)) = _
  simp [d8Rot_apply]

theorem d8Act_sr_zero (v : D8Mod p K) : d8Act (DihedralGroup.sr 0) v = (v.1⁻¹, v.2) := by
  rw [d8Act_sr]; simp [d8Ref_apply]

theorem d8Act_sr_one (v : D8Mod p K) : d8Act (DihedralGroup.sr 1) v = (v.2⁻¹, v.1⁻¹) := by
  rw [d8Act_sr]
  have : (1 : ZMod 4).val = 1 := by decide
  rw [this, pow_one]; rfl

theorem d8Act_sr_two (v : D8Mod p K) : d8Act (DihedralGroup.sr 2) v = (v.1, v.2⁻¹) := by
  rw [d8Act_sr]
  have : (2 : ZMod 4).val = 2 := by decide
  rw [this, pow_two]
  show d8Ref (d8Rot (d8Rot v)) = _
  simp [d8Rot_apply, d8Ref_apply]

theorem d8Act_sr_three (v : D8Mod p K) : d8Act (DihedralGroup.sr 3) v = (v.2, v.1) := by
  rw [d8Act_sr]
  have : (3 : ZMod 4).val = 3 := by decide
  rw [this, pow_succ, pow_two]
  show d8Ref (d8Rot (d8Rot (d8Rot v))) = _
  simp [d8Rot_apply, d8Ref_apply]

end CFSG.RankThree.PartOne.KFU
