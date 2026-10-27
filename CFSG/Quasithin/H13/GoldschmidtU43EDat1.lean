module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat3

public section

namespace CFSG.Quasithin.H13.U43

structure M16 where
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℕ)

namespace M16

@[expose] def eqB (a b : M16) : Bool :=
  (a.a0 == b.a0) && (a.a1 == b.a1) && (a.a2 == b.a2) && (a.a3 == b.a3) &&
  (a.a4 == b.a4) && (a.a5 == b.a5) && (a.a6 == b.a6) && (a.a7 == b.a7) &&
  (a.a8 == b.a8) && (a.a9 == b.a9) && (a.a10 == b.a10) && (a.a11 == b.a11) &&
  (a.a12 == b.a12) && (a.a13 == b.a13) && (a.a14 == b.a14) && (a.a15 == b.a15)

theorem eqB_iff {a b : M16} : eqB a b = true ↔ a = b := by
  cases a
  cases b
  simp [eqB, and_assoc]

instance : DecidableEq M16 := fun _ _ => decidable_of_iff _ eqB_iff

@[expose] def Valid (a : M16) : Prop :=
  a.a0 < 3 ∧ a.a1 < 3 ∧ a.a2 < 3 ∧ a.a3 < 3 ∧
    a.a4 < 3 ∧ a.a5 < 3 ∧ a.a6 < 3 ∧ a.a7 < 3 ∧
    a.a8 < 3 ∧ a.a9 < 3 ∧ a.a10 < 3 ∧ a.a11 < 3 ∧
    a.a12 < 3 ∧ a.a13 < 3 ∧ a.a14 < 3 ∧ a.a15 < 3

instance (a : M16) : Decidable (Valid a) := by unfold Valid; infer_instance

@[expose] def toMat (a : M16) : Mat3 :=
  !![(a.a0 : ZMod 3), (a.a1 : ZMod 3), (a.a2 : ZMod 3), (a.a3 : ZMod 3);
    (a.a4 : ZMod 3), (a.a5 : ZMod 3), (a.a6 : ZMod 3), (a.a7 : ZMod 3);
    (a.a8 : ZMod 3), (a.a9 : ZMod 3), (a.a10 : ZMod 3), (a.a11 : ZMod 3);
    (a.a12 : ZMod 3), (a.a13 : ZMod 3), (a.a14 : ZMod 3), (a.a15 : ZMod 3)]

@[expose] def mul (a b : M16) : M16 :=
  ⟨(a.a0 * b.a0 + a.a1 * b.a4 + a.a2 * b.a8 + a.a3 * b.a12) % 3,
   (a.a0 * b.a1 + a.a1 * b.a5 + a.a2 * b.a9 + a.a3 * b.a13) % 3,
   (a.a0 * b.a2 + a.a1 * b.a6 + a.a2 * b.a10 + a.a3 * b.a14) % 3,
   (a.a0 * b.a3 + a.a1 * b.a7 + a.a2 * b.a11 + a.a3 * b.a15) % 3,
   (a.a4 * b.a0 + a.a5 * b.a4 + a.a6 * b.a8 + a.a7 * b.a12) % 3,
   (a.a4 * b.a1 + a.a5 * b.a5 + a.a6 * b.a9 + a.a7 * b.a13) % 3,
   (a.a4 * b.a2 + a.a5 * b.a6 + a.a6 * b.a10 + a.a7 * b.a14) % 3,
   (a.a4 * b.a3 + a.a5 * b.a7 + a.a6 * b.a11 + a.a7 * b.a15) % 3,
   (a.a8 * b.a0 + a.a9 * b.a4 + a.a10 * b.a8 + a.a11 * b.a12) % 3,
   (a.a8 * b.a1 + a.a9 * b.a5 + a.a10 * b.a9 + a.a11 * b.a13) % 3,
   (a.a8 * b.a2 + a.a9 * b.a6 + a.a10 * b.a10 + a.a11 * b.a14) % 3,
   (a.a8 * b.a3 + a.a9 * b.a7 + a.a10 * b.a11 + a.a11 * b.a15) % 3,
   (a.a12 * b.a0 + a.a13 * b.a4 + a.a14 * b.a8 + a.a15 * b.a12) % 3,
   (a.a12 * b.a1 + a.a13 * b.a5 + a.a14 * b.a9 + a.a15 * b.a13) % 3,
   (a.a12 * b.a2 + a.a13 * b.a6 + a.a14 * b.a10 + a.a15 * b.a14) % 3,
   (a.a12 * b.a3 + a.a13 * b.a7 + a.a14 * b.a11 + a.a15 * b.a15) % 3⟩

@[expose] def one : M16 := ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

theorem toMat_mul (a b : M16) : toMat (mul a b) = toMat a * toMat b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, mul, Matrix.mul_apply, Fin.sum_univ_four, ZMod.natCast_mod]

theorem toMat_one : toMat one = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, one]

theorem valid_mul (a b : M16) : Valid (mul a b) := by
  unfold Valid mul
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Nat.mod_lt _ (by decide)

theorem toMat_inj {a b : M16} (ha : Valid a) (hb : Valid b) (h : toMat a = toMat b) : a = b := by
  have key : ∀ x : ℕ, x < 3 → ∀ y : ℕ, y < 3 → ((x : ℕ) : ZMod 3) = ((y : ℕ) : ZMod 3) → x = y := by
    decide
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
    ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
    hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩ := hb
  have e0 := key _ ha0 _ hb0 (by simpa [toMat] using congrFun (congrFun h 0) 0)
  have e1 := key _ ha1 _ hb1 (by simpa [toMat] using congrFun (congrFun h 0) 1)
  have e2 := key _ ha2 _ hb2 (by simpa [toMat] using congrFun (congrFun h 0) 2)
  have e3 := key _ ha3 _ hb3 (by simpa [toMat] using congrFun (congrFun h 0) 3)
  have e4 := key _ ha4 _ hb4 (by simpa [toMat] using congrFun (congrFun h 1) 0)
  have e5 := key _ ha5 _ hb5 (by simpa [toMat] using congrFun (congrFun h 1) 1)
  have e6 := key _ ha6 _ hb6 (by simpa [toMat] using congrFun (congrFun h 1) 2)
  have e7 := key _ ha7 _ hb7 (by simpa [toMat] using congrFun (congrFun h 1) 3)
  have e8 := key _ ha8 _ hb8 (by simpa [toMat] using congrFun (congrFun h 2) 0)
  have e9 := key _ ha9 _ hb9 (by simpa [toMat] using congrFun (congrFun h 2) 1)
  have e10 := key _ ha10 _ hb10 (by simpa [toMat] using congrFun (congrFun h 2) 2)
  have e11 := key _ ha11 _ hb11 (by simpa [toMat] using congrFun (congrFun h 2) 3)
  have e12 := key _ ha12 _ hb12 (by simpa [toMat] using congrFun (congrFun h 3) 0)
  have e13 := key _ ha13 _ hb13 (by simpa [toMat] using congrFun (congrFun h 3) 1)
  have e14 := key _ ha14 _ hb14 (by simpa [toMat] using congrFun (congrFun h 3) 2)
  have e15 := key _ ha15 _ hb15 (by simpa [toMat] using congrFun (congrFun h 3) 3)
  cases a
  cases b
  simp only at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  subst e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  rfl

end M16

structure V4 where
  (v0 v1 v2 v3 : ℕ)

namespace V4

@[expose] def eqB (a b : V4) : Bool :=
  (a.v0 == b.v0) && (a.v1 == b.v1) && (a.v2 == b.v2) && (a.v3 == b.v3)

theorem eqB_iff {a b : V4} : eqB a b = true ↔ a = b := by
  cases a
  cases b
  simp [eqB, and_assoc]

instance : DecidableEq V4 := fun _ _ => decidable_of_iff _ eqB_iff

@[expose] def toVec (v : V4) : Fin 4 → ZMod 3 := ![(v.v0 : ZMod 3), v.v1, v.v2, v.v3]

@[expose] def allV : List V4 :=
  [⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨2, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨2, 1, 0, 0⟩,
    ⟨0, 2, 0, 0⟩, ⟨1, 2, 0, 0⟩, ⟨2, 2, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, ⟨2, 0, 1, 0⟩,
    ⟨0, 1, 1, 0⟩, ⟨1, 1, 1, 0⟩, ⟨2, 1, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 2, 1, 0⟩, ⟨2, 2, 1, 0⟩,
    ⟨0, 0, 2, 0⟩, ⟨1, 0, 2, 0⟩, ⟨2, 0, 2, 0⟩, ⟨0, 1, 2, 0⟩, ⟨1, 1, 2, 0⟩, ⟨2, 1, 2, 0⟩,
    ⟨0, 2, 2, 0⟩, ⟨1, 2, 2, 0⟩, ⟨2, 2, 2, 0⟩, ⟨0, 0, 0, 1⟩, ⟨1, 0, 0, 1⟩, ⟨2, 0, 0, 1⟩,
    ⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩, ⟨2, 1, 0, 1⟩, ⟨0, 2, 0, 1⟩, ⟨1, 2, 0, 1⟩, ⟨2, 2, 0, 1⟩,
    ⟨0, 0, 1, 1⟩, ⟨1, 0, 1, 1⟩, ⟨2, 0, 1, 1⟩, ⟨0, 1, 1, 1⟩, ⟨1, 1, 1, 1⟩, ⟨2, 1, 1, 1⟩,
    ⟨0, 2, 1, 1⟩, ⟨1, 2, 1, 1⟩, ⟨2, 2, 1, 1⟩, ⟨0, 0, 2, 1⟩, ⟨1, 0, 2, 1⟩, ⟨2, 0, 2, 1⟩,
    ⟨0, 1, 2, 1⟩, ⟨1, 1, 2, 1⟩, ⟨2, 1, 2, 1⟩, ⟨0, 2, 2, 1⟩, ⟨1, 2, 2, 1⟩, ⟨2, 2, 2, 1⟩,
    ⟨0, 0, 0, 2⟩, ⟨1, 0, 0, 2⟩, ⟨2, 0, 0, 2⟩, ⟨0, 1, 0, 2⟩, ⟨1, 1, 0, 2⟩, ⟨2, 1, 0, 2⟩,
    ⟨0, 2, 0, 2⟩, ⟨1, 2, 0, 2⟩, ⟨2, 2, 0, 2⟩, ⟨0, 0, 1, 2⟩, ⟨1, 0, 1, 2⟩, ⟨2, 0, 1, 2⟩,
    ⟨0, 1, 1, 2⟩, ⟨1, 1, 1, 2⟩, ⟨2, 1, 1, 2⟩, ⟨0, 2, 1, 2⟩, ⟨1, 2, 1, 2⟩, ⟨2, 2, 1, 2⟩,
    ⟨0, 0, 2, 2⟩, ⟨1, 0, 2, 2⟩, ⟨2, 0, 2, 2⟩, ⟨0, 1, 2, 2⟩, ⟨1, 1, 2, 2⟩, ⟨2, 1, 2, 2⟩,
    ⟨0, 2, 2, 2⟩, ⟨1, 2, 2, 2⟩, ⟨2, 2, 2, 2⟩]

@[expose] def mulV (a : M16) (v : V4) : V4 :=
  ⟨(a.a0 * v.v0 + a.a1 * v.v1 + a.a2 * v.v2 + a.a3 * v.v3) % 3,
    (a.a4 * v.v0 + a.a5 * v.v1 + a.a6 * v.v2 + a.a7 * v.v3) % 3,
    (a.a8 * v.v0 + a.a9 * v.v1 + a.a10 * v.v2 + a.a11 * v.v3) % 3,
    (a.a12 * v.v0 + a.a13 * v.v1 + a.a14 * v.v2 + a.a15 * v.v3) % 3⟩

theorem toVec_mulV (a : M16) (v : V4) :
    toVec (mulV a v) = (M16.toMat a).mulVec (toVec v) := by
  ext i
  fin_cases i <;>
    simp [toVec, mulV, M16.toMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ZMod.natCast_mod]

theorem exists_toVec (v : Fin 4 → ZMod 3) : ∃ w ∈ allV, toVec w = v := by
  have hmem : ∀ a b c d : ZMod 3, (⟨a.val, b.val, c.val, d.val⟩ : V4) ∈ allV := by decide
  refine ⟨⟨(v 0).val, (v 1).val, (v 2).val, (v 3).val⟩, hmem _ _ _ _, ?_⟩
  ext i
  fin_cases i <;> simp [toVec]

end V4

end CFSG.Quasithin.H13.U43
