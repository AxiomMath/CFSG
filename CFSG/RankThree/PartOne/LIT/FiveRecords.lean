module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix

instance instFactPrimeFiveLIT : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 5)

structure R3 where
  a00 : ℕ
  a01 : ℕ
  a02 : ℕ
  a10 : ℕ
  a11 : ℕ
  a12 : ℕ
  a20 : ℕ
  a21 : ℕ
  a22 : ℕ

instance instDecidableEqR3 : DecidableEq R3 := fun r s =>
  decidable_of_iff (r.a00 = s.a00 ∧ r.a01 = s.a01 ∧ r.a02 = s.a02 ∧ r.a10 = s.a10 ∧
    r.a11 = s.a11 ∧ r.a12 = s.a12 ∧ r.a20 = s.a20 ∧ r.a21 = s.a21 ∧ r.a22 = s.a22)
    (by
      constructor
      · rintro ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩
        cases r
        cases s
        simp_all
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

namespace R3

@[expose] def mul (r s : R3) : R3 :=
  ⟨(r.a00 * s.a00 + r.a01 * s.a10 + r.a02 * s.a20) % 5,
   (r.a00 * s.a01 + r.a01 * s.a11 + r.a02 * s.a21) % 5,
   (r.a00 * s.a02 + r.a01 * s.a12 + r.a02 * s.a22) % 5,
   (r.a10 * s.a00 + r.a11 * s.a10 + r.a12 * s.a20) % 5,
   (r.a10 * s.a01 + r.a11 * s.a11 + r.a12 * s.a21) % 5,
   (r.a10 * s.a02 + r.a11 * s.a12 + r.a12 * s.a22) % 5,
   (r.a20 * s.a00 + r.a21 * s.a10 + r.a22 * s.a20) % 5,
   (r.a20 * s.a01 + r.a21 * s.a11 + r.a22 * s.a21) % 5,
   (r.a20 * s.a02 + r.a21 * s.a12 + r.a22 * s.a22) % 5⟩

@[expose] def transpose (r : R3) : R3 :=
  ⟨r.a00, r.a10, r.a20, r.a01, r.a11, r.a21, r.a02, r.a12, r.a22⟩

@[expose] def one : R3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def Norm (r : R3) : Prop :=
  r.a00 < 5 ∧ r.a01 < 5 ∧ r.a02 < 5 ∧ r.a10 < 5 ∧ r.a11 < 5 ∧ r.a12 < 5 ∧ r.a20 < 5 ∧
    r.a21 < 5 ∧ r.a22 < 5

@[expose] def toM (r : R3) : M3 :=
  !![(r.a00 : ZMod 5), r.a01, r.a02; r.a10, r.a11, r.a12; r.a20, r.a21, r.a22]

@[expose] def ofM (A : M3) : R3 :=
  ⟨(A 0 0).val, (A 0 1).val, (A 0 2).val, (A 1 0).val, (A 1 1).val, (A 1 2).val, (A 2 0).val,
    (A 2 1).val, (A 2 2).val⟩

theorem norm_ofM (A : M3) : (ofM A).Norm :=
  ⟨ZMod.val_lt (A 0 0), ZMod.val_lt (A 0 1), ZMod.val_lt (A 0 2), ZMod.val_lt (A 1 0),
    ZMod.val_lt (A 1 1), ZMod.val_lt (A 1 2), ZMod.val_lt (A 2 0), ZMod.val_lt (A 2 1),
    ZMod.val_lt (A 2 2)⟩

theorem norm_mul (r s : R3) : (mul r s).Norm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.mod_lt _ (by norm_num)

theorem norm_transpose {r : R3} (h : r.Norm) : r.transpose.Norm := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := h
  exact ⟨h00, h10, h20, h01, h11, h21, h02, h12, h22⟩

theorem norm_one : one.Norm := by
  unfold Norm one
  decide

theorem toM_ofM (A : M3) : (ofM A).toM = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofM, toM]

theorem toM_mul (r s : R3) : (mul r s).toM = r.toM * s.toM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul, toM, Matrix.mul_apply, Fin.sum_univ_three, ZMod.natCast_mod]

theorem toM_transpose (r : R3) : r.transpose.toM = r.toMᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transpose, toM]

theorem toM_one : one.toM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one, toM]

theorem toM_injOn {r s : R3} (hr : r.Norm) (hs : s.Norm) (h : r.toM = s.toM) : r = s := by
  obtain ⟨hr00, hr01, hr02, hr10, hr11, hr12, hr20, hr21, hr22⟩ := hr
  obtain ⟨hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22⟩ := hs
  have e : ∀ i j, r.toM i j = s.toM i j := fun i j => by rw [h]
  have key : ∀ x y : ℕ, x < 5 → y < 5 → (x : ZMod 5) = (y : ZMod 5) → x = y := by
    intro x y hx hy hxy
    have := (ZMod.natCast_eq_natCast_iff' x y 5).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have e00 := key _ _ hr00 hs00 (by simpa [toM] using e 0 0)
  have e01 := key _ _ hr01 hs01 (by simpa [toM] using e 0 1)
  have e02 := key _ _ hr02 hs02 (by simpa [toM] using e 0 2)
  have e10 := key _ _ hr10 hs10 (by simpa [toM] using e 1 0)
  have e11 := key _ _ hr11 hs11 (by simpa [toM] using e 1 1)
  have e12 := key _ _ hr12 hs12 (by simpa [toM] using e 1 2)
  have e20 := key _ _ hr20 hs20 (by simpa [toM] using e 2 0)
  have e21 := key _ _ hr21 hs21 (by simpa [toM] using e 2 1)
  have e22 := key _ _ hr22 hs22 (by simpa [toM] using e 2 2)
  cases r
  cases s
  simp_all

theorem ofM_mul (A B : M3) : ofM (A * B) = mul (ofM A) (ofM B) := by
  apply toM_injOn (norm_ofM _) (norm_mul _ _)
  rw [toM_ofM, toM_mul, toM_ofM, toM_ofM]

theorem ofM_transpose (A : M3) : ofM Aᵀ = transpose (ofM A) := by
  apply toM_injOn (norm_ofM _) (norm_transpose (norm_ofM _))
  rw [toM_ofM, toM_transpose, toM_ofM]

theorem ofM_one : ofM (1 : M3) = one := by
  apply toM_injOn (norm_ofM _) norm_one
  rw [toM_ofM, toM_one]

theorem ofM_inj {A B : M3} (h : ofM A = ofM B) : A = B := by
  rw [← toM_ofM A, ← toM_ofM B, h]

end R3

end CFSG.RankThree.PartOne.LIT
