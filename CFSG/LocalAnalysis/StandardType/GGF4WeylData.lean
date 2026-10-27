module

public section

namespace CFSG.StandardType.F4Model

structure M4 where
  m00 : Int
  m01 : Int
  m02 : Int
  m03 : Int
  m10 : Int
  m11 : Int
  m12 : Int
  m13 : Int
  m20 : Int
  m21 : Int
  m22 : Int
  m23 : Int
  m30 : Int
  m31 : Int
  m32 : Int
  m33 : Int
  deriving @[expose] DecidableEq

namespace M4

@[expose] def one : M4 := ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] def mul (x y : M4) : M4 :=
  ⟨x.m00 * y.m00 + x.m01 * y.m10 + x.m02 * y.m20 + x.m03 * y.m30,
   x.m00 * y.m01 + x.m01 * y.m11 + x.m02 * y.m21 + x.m03 * y.m31,
   x.m00 * y.m02 + x.m01 * y.m12 + x.m02 * y.m22 + x.m03 * y.m32,
   x.m00 * y.m03 + x.m01 * y.m13 + x.m02 * y.m23 + x.m03 * y.m33,
   x.m10 * y.m00 + x.m11 * y.m10 + x.m12 * y.m20 + x.m13 * y.m30,
   x.m10 * y.m01 + x.m11 * y.m11 + x.m12 * y.m21 + x.m13 * y.m31,
   x.m10 * y.m02 + x.m11 * y.m12 + x.m12 * y.m22 + x.m13 * y.m32,
   x.m10 * y.m03 + x.m11 * y.m13 + x.m12 * y.m23 + x.m13 * y.m33,
   x.m20 * y.m00 + x.m21 * y.m10 + x.m22 * y.m20 + x.m23 * y.m30,
   x.m20 * y.m01 + x.m21 * y.m11 + x.m22 * y.m21 + x.m23 * y.m31,
   x.m20 * y.m02 + x.m21 * y.m12 + x.m22 * y.m22 + x.m23 * y.m32,
   x.m20 * y.m03 + x.m21 * y.m13 + x.m22 * y.m23 + x.m23 * y.m33,
   x.m30 * y.m00 + x.m31 * y.m10 + x.m32 * y.m20 + x.m33 * y.m30,
   x.m30 * y.m01 + x.m31 * y.m11 + x.m32 * y.m21 + x.m33 * y.m31,
   x.m30 * y.m02 + x.m31 * y.m12 + x.m32 * y.m22 + x.m33 * y.m32,
   x.m30 * y.m03 + x.m31 * y.m13 + x.m32 * y.m23 + x.m33 * y.m33⟩

end M4

@[expose] def Sdata : List M4 := [⟨-1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 1, -1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 2, -1, 1, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, -1⟩]

@[expose] def Sm (i : Fin 4) : M4 := Sdata.getD i.val M4.one

@[expose] def Rdata : List M4 := [⟨-1, 0, 0, 0, -3, 1, 0, 0, -4, 0, 1, 0, -2, 0, 0, 1⟩,
  ⟨-1, 0, 0, 1, -2, 1, 0, 1, -2, 0, 1, 1, 0, 0, 0, 1⟩,
  ⟨-1, 0, 1, -1, -2, 1, 1, -1, -2, 0, 2, -1, -2, 0, 1, 0⟩,
  ⟨-1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
  ⟨-1, 2, -1, 0, -2, 3, -1, 0, -4, 4, -1, 0, -2, 2, -1, 1⟩,
  ⟨0, -1, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
  ⟨0, 1, -1, 1, -1, 2, -1, 1, -2, 2, -1, 2, 0, 0, 0, 1⟩,
  ⟨0, 1, 0, -1, -1, 2, 0, -1, -2, 2, 1, -2, -2, 2, 0, -1⟩,
  ⟨1, -2, 1, 0, 0, -3, 2, 0, 0, -4, 3, 0, 0, -2, 1, 1⟩,
  ⟨1, -1, 0, 1, 0, -1, 0, 2, 0, -2, 1, 2, 0, 0, 0, 1⟩,
  ⟨1, -1, 1, -1, 0, -1, 2, -2, 0, -2, 3, -2, 0, -2, 2, -1⟩,
  ⟨1, 0, -1, 1, 0, 1, -2, 2, 0, 0, -2, 3, 0, 0, -1, 2⟩,
  ⟨1, 0, 0, -1, 0, 1, 0, -2, 0, 0, 1, -3, 0, 0, 0, -1⟩,
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, -1⟩,
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 2, -1, 1, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -1, 0, 2, -1, 0⟩,
  ⟨1, 0, 0, 0, 1, -1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 1, 1, -1, 1, 2, 0, -1, 2, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 1, 1, 0, -1, 2, 0, 1, -2, 2, 0, 0, -1⟩,
  ⟨1, 0, 0, 0, 2, -1, 0, 1, 2, -2, 1, 1, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 2, -1, 1, -1, 2, -2, 2, -1, 2, -2, 1, 0⟩,
  ⟨1, 0, 0, 0, 2, 1, -1, 0, 4, 0, -1, 0, 2, 0, -1, 1⟩,
  ⟨1, 1, -1, 0, 0, 3, -2, 0, 0, 4, -3, 0, 0, 2, -2, 1⟩,
  ⟨2, -1, 0, 0, 3, -2, 0, 0, 4, -4, 1, 0, 2, -2, 0, 1⟩]

@[expose] def Rm (x : Nat) : M4 := Rdata.getD x M4.one

@[expose] def evalW (l : List (Fin 4)) : M4 := l.foldr (fun i m => (Sm i).mul m) M4.one

@[expose] def conjW (w : List (Fin 4)) (x : M4) : M4 := (evalW w).mul (x.mul (evalW w.reverse))

@[expose] def pw2 (z : M4) : M4 := z.mul z

@[expose] def pw3 (z : M4) : M4 := z.mul (z.mul z)

@[expose] def pw4 (z : M4) : M4 := (z.mul z).mul (z.mul z)

@[expose] def relb (a₀ a₁ a₂ : M4) : Bool :=
  pw3 (a₀.mul a₁) == M4.one && a₀.mul a₁ != M4.one && pw4 (a₁.mul a₂) == M4.one &&
    pw2 (a₁.mul a₂) != M4.one && pw2 (a₀.mul a₂) == M4.one && a₀.mul a₂ != M4.one

@[expose] def relM (a₀ a₁ a₂ : M4) : Prop := relb a₀ a₁ a₂ = true

instance (a₀ a₁ a₂ : M4) : Decidable (relM a₀ a₁ a₂) := inferInstanceAs (Decidable (relb a₀ a₁ a₂ = true))

theorem relM_iff (a₀ a₁ a₂ : M4) : relM a₀ a₁ a₂ ↔
    (pw3 (a₀.mul a₁) = M4.one ∧ a₀.mul a₁ ≠ M4.one ∧ pw4 (a₁.mul a₂) = M4.one ∧
      pw2 (a₁.mul a₂) ≠ M4.one ∧ pw2 (a₀.mul a₂) = M4.one ∧ a₀.mul a₂ ≠ M4.one) := by
  simp [relM, relb, Bool.and_eq_true, and_assoc]

@[expose] def T1data : List (Fin 4) :=
  [1,
   2,
   2,
   1,
   2,
   1,
   1,
   1,
   2,
   1,
   1,
   2,
   2,
   2,
   2,
   2,
   1,
   1,
   1,
   2,
   2,
   2,
   1,
   1]

@[expose] def W1data : List (List (Fin 4)) :=
  [[2, 3, 0, 1, 2, 1, 0],
   [1, 0],
   [3, 1, 0],
   [0, 1],
   [3, 1, 2, 0],
   [0],
   [2, 0],
   [2, 3, 0],
   [3, 1, 2, 0, 1],
   [2, 0, 1],
   [2, 3, 0, 1],
   [3, 1, 2, 0, 1, 2],
   [3, 1, 2, 0, 1, 2, 3],
   [3, 2],
   [],
   [3],
   [],
   [2],
   [2, 3],
   [1],
   [3, 1],
   [3, 1, 2],
   [2, 3, 0, 1, 2],
   [2, 3, 0, 1, 2, 1]]

@[expose] def W2Bdata : List (List (Fin 4)) :=
  [[3, 2, 1, 2, 0, 1, 2, 0, 1, 0],
   [],
   [3],
   [3, 2, 1, 2, 0, 1, 2, 1, 0],
   [1],
   [3, 1],
   [3, 0, 1, 2, 0, 1, 0],
   [3, 2, 1, 2],
   [2, 1, 2],
   [0, 1, 2, 3, 2, 0, 1, 0],
   [3, 2, 1, 2, 3],
   [2, 1, 2, 3],
   [3, 0, 1, 2, 1, 0],
   [2, 1, 2, 1],
   [3, 2, 1, 2, 1],
   [0, 1, 2, 3, 2, 1, 0],
   [2, 1, 2, 3, 1],
   [3, 2, 1, 2, 3, 1],
   [0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 1],
   [3, 2, 1, 2, 3, 2, 1, 2],
   [2, 1, 2, 3, 2, 1, 2],
   [0, 1, 2, 3, 2, 1, 2, 0, 1, 2],
   [3, 2, 1, 2, 3, 2, 1, 2, 1],
   [2, 1, 2, 3, 2, 1, 2, 1]]

@[expose] def W2Cdata : List (List (Fin 4)) :=
  [[1, 2, 1, 0],
   [0, 1, 2, 1, 0],
   [3, 2, 0, 1, 2, 3, 2, 0],
   [2, 1, 2, 1, 0],
   [3, 2, 0, 1, 2, 3, 0],
   [2, 0, 1, 2, 1, 0],
   [1, 2, 0, 1, 2, 0, 1],
   [1, 2, 0, 1, 2, 0, 1, 0],
   [3, 2, 0, 1, 2, 3, 2, 0, 1, 2, 1],
   [2, 1, 2, 0, 1, 2, 0, 1],
   [3, 2, 0, 1, 2, 3, 0, 1, 2, 1],
   [2, 1, 2, 0, 1, 2, 0, 1, 0],
   [0],
   [],
   [3, 2, 0, 1, 2, 3, 2, 1, 2, 1],
   [2, 0],
   [3, 2, 0, 1, 2, 3, 1, 2, 1],
   [2],
   [0, 1, 2, 1],
   [1, 2, 1],
   [3, 2, 0, 1, 2, 3, 2],
   [2, 0, 1, 2, 1],
   [3, 2, 0, 1, 2, 3],
   [2, 1, 2, 1]]

@[expose] def WBdata : List (List (Fin 4)) :=
  [[],
   [],
   [0, 1, 2],
   [],
   [2, 0, 1, 2],
   [],
   [],
   [],
   [1, 2, 0, 1, 2],
   [],
   [],
   [2, 1, 2, 0, 1, 2],
   [],
   [],
   [],
   [2],
   [],
   [],
   [],
   [],
   [1, 2],
   [2, 1, 2],
   [],
   []]

@[expose] def WCdata : List (List (Fin 4)) :=
  [[],
   [],
   [],
   [],
   [],
   [1],
   [2, 1],
   [3, 2, 1],
   [],
   [1, 2, 1],
   [1, 3, 2, 1],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [2, 1, 3, 2, 1],
   [1, 2, 1, 3, 2, 1]]

@[expose] def ClB : List Nat := [1, 12, 14, 19]

@[expose] def ClC : List Nat := [0, 16, 17, 18]

@[expose] def T1 (x : Nat) : Fin 4 := T1data.getD x 0
@[expose] def W1 (x : Nat) : List (Fin 4) := W1data.getD x []
@[expose] def W2B (k : Nat) : List (Fin 4) := W2Bdata.getD k []
@[expose] def W2C (k : Nat) : List (Fin 4) := W2Cdata.getD k []
@[expose] def WB (y : Nat) : List (Fin 4) := WBdata.getD y []
@[expose] def WC (y : Nat) : List (Fin 4) := WCdata.getD y []
abbrev normM (y : M4) (Cl : List Nat) : Prop :=
  ∀ c ∈ Cl, ∃ c' ∈ Cl, y.mul ((Rm c).mul y) = Rm c'

theorem Sm_sq : ∀ i : Fin 4, (Sm i).mul (Sm i) = M4.one := by decide +kernel

theorem Rm_sq : ∀ x, x < 24 → (Rm x).mul (Rm x) = M4.one := by decide +kernel

theorem Sm_mem_R : ∀ j : Fin 4, ∃ x, x < 24 ∧ Sm j = Rm x := by decide +kernel

theorem R_conj_closed :
    ∀ i : Fin 4, ∀ x, x < 24 → ∃ y, y < 24 ∧ (Sm i).mul ((Rm x).mul (Sm i)) = Rm y := by
  decide +kernel

theorem stage1 :
    ∀ x, x < 24 → (T1 x = 1 ∨ T1 x = 2) ∧ conjW (W1 x) (Rm x) = Sm (T1 x) := by
  decide +kernel

theorem stage2B :
    ∀ x₀, x₀ < 24 → ∀ x₂, x₂ < 24 → relM (Rm x₀) (Sm 1) (Rm x₂) →
      ∃ k, k < 24 ∧ conjW (W2B k) (Rm x₀) = Sm 0 ∧ conjW (W2B k) (Rm x₂) = Sm 2 ∧
        conjW (W2B k) (Sm 1) = Sm 1 := by
  decide +kernel

theorem stage2C :
    ∀ x₀, x₀ < 24 → ∀ x₂, x₂ < 24 → relM (Rm x₀) (Sm 2) (Rm x₂) →
      ∃ k, k < 24 ∧ conjW (W2C k) (Rm x₀) = Sm 3 ∧ conjW (W2C k) (Rm x₂) = Sm 1 ∧
        conjW (W2C k) (Sm 2) = Sm 2 := by
  decide +kernel

theorem dichB :
    ∀ y, y < 24 → normM (Rm y) ClB ∨ (conjW (WB y) (Sm 3) = Rm y ∧ ∀ i ∈ WB y, i ≠ 3) := by
  decide +kernel

theorem dichC :
    ∀ y, y < 24 → normM (Rm y) ClC ∨ (conjW (WC y) (Sm 0) = Rm y ∧ ∀ i ∈ WC y, i ≠ 0) := by
  decide +kernel

theorem stdB_norm : normM (Sm 0) ClB ∧ normM (Sm 1) ClB ∧ normM (Sm 2) ClB := by decide +kernel

theorem stdC_norm : normM (Sm 3) ClC ∧ normM (Sm 2) ClC ∧ normM (Sm 1) ClC := by decide +kernel

theorem stdB_mem : ∃ c ∈ ClB, Sm 2 = Rm c := by decide +kernel

theorem stdC_mem : ∃ c ∈ ClC, Sm 1 = Rm c := by decide +kernel

theorem stdB_notnorm : ∀ c' ∈ ClB, (Sm 3).mul ((Sm 2).mul (Sm 3)) ≠ Rm c' := by decide +kernel

theorem stdC_notnorm : ∀ c' ∈ ClC, (Sm 0).mul ((Sm 1).mul (Sm 0)) ≠ Rm c' := by decide +kernel

end CFSG.StandardType.F4Model
