module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK
public import CFSG.RankThree.PartTwo.Sec21.Hering2119KData

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

@[expose] def V4C.toV (v : V4C) : V4 := ![(v.a : F3), (v.b : F3), (v.c : F3), (v.d : F3)]

@[expose] def M4C.toM (A : M4C) : M4 :=
  !![
    (A.m00 : F3), (A.m01 : F3), (A.m02 : F3), (A.m03 : F3);
    (A.m10 : F3), (A.m11 : F3), (A.m12 : F3), (A.m13 : F3);
    (A.m20 : F3), (A.m21 : F3), (A.m22 : F3), (A.m23 : F3);
    (A.m30 : F3), (A.m31 : F3), (A.m32 : F3), (A.m33 : F3)]

@[expose] def V4C.Valid (v : V4C) : Prop := v.a < 3 ∧ v.b < 3 ∧ v.c < 3 ∧ v.d < 3

theorem V4C.toV_add (x y : V4C) : (x.add y).toV = x.toV + y.toV := by
  ext i
  fin_cases i <;> simp [V4C.add, V4C.toV, ZMod.natCast_mod]

theorem V4C.toV_smul (k : Nat) (x : V4C) : (x.smul k).toV = (k : F3) • x.toV := by
  ext i
  fin_cases i <;> simp [V4C.smul, V4C.toV, ZMod.natCast_mod]

theorem M4C.toM_mul (A B : M4C) : (A.mul B).toM = A.toM * B.toM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M4C.mul, M4C.toM, Matrix.mul_apply, Fin.sum_univ_four, ZMod.natCast_mod]

theorem M4C.toV_mv (A : M4C) (v : V4C) : (A.mv v).toV = A.toM.mulVec v.toV := by
  ext i
  fin_cases i <;>
    simp [M4C.mv, V4C.toV, M4C.toM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ZMod.natCast_mod]

theorem M4C.toM_one : M4C.one.toM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M4C.one, M4C.toM]

theorem V4C.om_spec (x y : V4C) : ((x.om y : Nat) : F3) = omega4 x.toV y.toV := by
  have key : ∀ a b c d a' b' c' d' : F3,
      a * c' + 2 * (c * a') + b * d' + 2 * (d * b') = a * c' - c * a' + b * d' - d * b' := by
    decide +kernel
  simp only [V4C.om, omega4, V4C.toV, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod,
    Nat.cast_ofNat]
  exact key _ _ _ _ _ _ _ _

@[expose] def M4C.Valid (A : M4C) : Prop :=
  A.m00 < 3 ∧ A.m01 < 3 ∧ A.m02 < 3 ∧ A.m03 < 3 ∧ A.m10 < 3 ∧ A.m11 < 3 ∧ A.m12 < 3 ∧ A.m13 < 3 ∧
  A.m20 < 3 ∧ A.m21 < 3 ∧ A.m22 < 3 ∧ A.m23 < 3 ∧ A.m30 < 3 ∧ A.m31 < 3 ∧ A.m32 < 3 ∧ A.m33 < 3

theorem nat_eq_of_cast_eq {a b : Nat} (ha : a < 3) (hb : b < 3) (h : (a : F3) = (b : F3)) :
    a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b 3).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem V4C.toV_inj {x y : V4C} (hx : x.Valid) (hy : y.Valid) (h : x.toV = y.toV) : x = y := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [V4C.toV] at h0 h1 h2 h3
  cases x; cases y
  simp only [V4C.mk.injEq]
  exact ⟨nat_eq_of_cast_eq hx1 hy1 h0, nat_eq_of_cast_eq hx2 hy2 h1, nat_eq_of_cast_eq hx3 hy3 h2,
    nat_eq_of_cast_eq hx4 hy4 h3⟩

theorem M4C.toM_inj {A B : M4C} (hA : A.Valid) (hB : B.Valid) (h : A.toM = B.toM) : A = B := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hA
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ := hB
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h13 := congrFun (congrFun h 1) 3
  have h20 := congrFun (congrFun h 2) 0
  have h21 := congrFun (congrFun h 2) 1
  have h22 := congrFun (congrFun h 2) 2
  have h23 := congrFun (congrFun h 2) 3
  have h30 := congrFun (congrFun h 3) 0
  have h31 := congrFun (congrFun h 3) 1
  have h32 := congrFun (congrFun h 3) 2
  have h33 := congrFun (congrFun h 3) 3
  simp [M4C.toM] at h00 h01 h02 h03 h10 h11 h12 h13 h20 h21 h22 h23 h30 h31 h32 h33
  cases A; cases B
  simp only [M4C.mk.injEq]
  exact ⟨nat_eq_of_cast_eq a0 b0 h00, nat_eq_of_cast_eq a1 b1 h01, nat_eq_of_cast_eq a2 b2 h02,
    nat_eq_of_cast_eq a3 b3 h03, nat_eq_of_cast_eq a4 b4 h10, nat_eq_of_cast_eq a5 b5 h11,
    nat_eq_of_cast_eq a6 b6 h12, nat_eq_of_cast_eq a7 b7 h13, nat_eq_of_cast_eq a8 b8 h20,
    nat_eq_of_cast_eq a9 b9 h21, nat_eq_of_cast_eq a10 b10 h22, nat_eq_of_cast_eq a11 b11 h23,
    nat_eq_of_cast_eq a12 b12 h30, nat_eq_of_cast_eq a13 b13 h31, nat_eq_of_cast_eq a14 b14 h32,
    nat_eq_of_cast_eq a15 b15 h33⟩

theorem V4C.valid_of_mod (a b c d : Nat) :
    (V4C.mk (a % 3) (b % 3) (c % 3) (d % 3)).Valid :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num)⟩

theorem M4C.valid_mul (A B : M4C) : (A.mul B).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Nat.mod_lt _ (by norm_num)

theorem M4C.valid_mv (A : M4C) (v : V4C) : (A.mv v).Valid :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num)⟩

theorem M4C.valid_one : M4C.one.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem V4C.valid_add (x y : V4C) : (x.add y).Valid := V4C.valid_of_mod _ _ _ _

@[expose] def toCV (v : V4) : V4C := ⟨(v 0).val, (v 1).val, (v 2).val, (v 3).val⟩

@[expose] def toCM (X : M4) : M4C :=
  ⟨(X 0 0).val, (X 0 1).val, (X 0 2).val, (X 0 3).val, (X 1 0).val, (X 1 1).val, (X 1 2).val,
   (X 1 3).val, (X 2 0).val, (X 2 1).val, (X 2 2).val, (X 2 3).val, (X 3 0).val, (X 3 1).val,
   (X 3 2).val, (X 3 3).val⟩

theorem toV_toCV (v : V4) : (toCV v).toV = v := by
  ext i
  fin_cases i <;> simp [toCV, V4C.toV]

theorem toM_toCM (X : M4) : (toCM X).toM = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toCM, M4C.toM]

theorem valid_toCV (v : V4) : (toCV v).Valid :=
  ⟨ZMod.val_lt (v 0), ZMod.val_lt (v 1), ZMod.val_lt (v 2), ZMod.val_lt (v 3)⟩

theorem valid_toCM (X : M4) : (toCM X).Valid :=
  ⟨ZMod.val_lt (X 0 0), ZMod.val_lt (X 0 1), ZMod.val_lt (X 0 2), ZMod.val_lt (X 0 3),
   ZMod.val_lt (X 1 0), ZMod.val_lt (X 1 1), ZMod.val_lt (X 1 2), ZMod.val_lt (X 1 3),
   ZMod.val_lt (X 2 0), ZMod.val_lt (X 2 1), ZMod.val_lt (X 2 2), ZMod.val_lt (X 2 3),
   ZMod.val_lt (X 3 0), ZMod.val_lt (X 3 1), ZMod.val_lt (X 3 2), ZMod.val_lt (X 3 3)⟩

theorem mem_allVecs_of_valid {v : V4C} (hv : v.Valid) : v ∈ allVecs := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  simp only [allVecs, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨v.a, h1, v.b, h2, v.c, h3, v.d, h4, rfl⟩

theorem valid_of_mem_allVecs {v : V4C} (hv : v ∈ allVecs) : v.Valid := by
  simp only [allVecs, List.mem_flatMap, List.mem_range, List.mem_map] at hv
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hv
  exact ⟨ha, hb, hc, hd⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
