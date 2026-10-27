
module

public import CFSG.Sporadic.Th.Max3.QuotientBase
public import CFSG.Sporadic.ThSchreier.Enc8
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

@[expose] def posWord {G : Type*} [Monoid G] (g h : G) (w : List ℕ) : G :=
  (w.map fun l => if l = 1 then g else h).prod

theorem posWord_nil {G : Type*} [Monoid G] (g h : G) : posWord g h [] = 1 := rfl

theorem posWord_cons {G : Type*} [Monoid G] (g h : G) (l : ℕ) (w : List ℕ) :
    posWord g h (l :: w) = (if l = 1 then g else h) * posWord g h w := rfl

theorem map_posWord {G G' : Type*} [Monoid G] [Monoid G'] (f : G →* G') (g h : G)
    (w : List ℕ) : f (posWord g h w) = posWord (f g) (f h) w := by
  induction w with
  | nil => simp [posWord_nil]
  | cons l w ih =>
    rw [posWord_cons, posWord_cons, map_mul, ih]
    split_ifs <;> rfl

@[expose] def tPerm : Equiv.Perm (Fin 9) := Equiv.swap 0 1

@[expose] def oddD1 : Matrix (Fin 8) (Fin 8) (ZMod 2) := posWord B1 B2 oddWord1

@[expose] def oddD2 : Matrix (Fin 8) (Fin 8) (ZMod 2) := posWord B1 B2 oddWord2

theorem oddWords_perm : posWord aPerm bPerm oddWord1 = tPerm * aPerm * tPerm⁻¹ ∧
    posWord aPerm bPerm oddWord2 = tPerm * bPerm * tPerm⁻¹ := by
  decide

theorem mul_posWord_of_intertwine {T C₁ C₂ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h₁ : T * B1 = C₁ * T) (h₂ : T * B2 = C₂ * T) (w : List ℕ) :
    T * posWord B1 B2 w = posWord C₁ C₂ w * T := by
  induction w with
  | nil => simp [posWord_nil]
  | cons l w ih =>
    rw [posWord_cons, posWord_cons]
    split_ifs
    · rw [← Matrix.mul_assoc, h₁, Matrix.mul_assoc, ih, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, h₂, Matrix.mul_assoc, ih, Matrix.mul_assoc]

@[expose] def basisWords : Fin 8 → List ℕ :=
  ![[], [1], [2, 1], [1, 2, 1], [2, 1, 2, 1], [1, 2, 1, 2, 1], [2, 2, 1, 2, 1], [1, 2, 2, 1, 2, 1]]

@[expose] def e0 : Fin 8 → ZMod 2 := Pi.single 0 1

@[expose] def colMat (C₁ C₂ : Matrix (Fin 8) (Fin 8) (ZMod 2)) (u : Fin 8 → ZMod 2) :
    Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i k => (posWord C₁ C₂ (basisWords k)).mulVec u i

@[expose] def basisP : Matrix (Fin 8) (Fin 8) (ZMod 2) := colMat B1 B2 e0

@[expose] def basisPInv : Matrix (Fin 8) (Fin 8) (ZMod 2) := mat8 basisPInvEnc

theorem mat8_B1enc : mat8 B1enc = B1 := by
  ext i j
  rw [B1_eq_testBit]
  simp only [mat8, Matrix.of_apply, bitZ]
  fin_cases j <;> rfl

theorem mat8_B2enc : mat8 B2enc = B2 := by
  ext i j
  rw [B2_eq_testBit]
  simp only [mat8, Matrix.of_apply, bitZ]
  fin_cases j <;> rfl

theorem mat8_posWord8 (A B : List ℕ) (w : List ℕ) :
    mat8 (posWord8 A B w) = posWord (mat8 A) (mat8 B) w := by
  induction w with
  | nil => exact mat8_id8
  | cons l w ih =>
    rw [posWord8, List.foldr_cons, ← posWord8, mat8_mul, ih, posWord_cons]
    split_ifs <;> rfl

theorem basisWords_eq (k : Fin 8) : basisWords k = basisWordsL.getD k [] := by
  fin_cases k <;> rfl

theorem mat8_colMat8 (C₁ C₂ : List ℕ) (u : ℕ) :
    mat8 (colMat8 C₁ C₂ u) = colMat (mat8 C₁) (mat8 C₂) (vec8 u) := by
  ext i k
  change bitZ ((colMat8 C₁ C₂ u).getD k 0) i =
    (posWord (mat8 C₁) (mat8 C₂) (basisWords k)).mulVec (vec8 u) i
  rw [colMat8, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
    basisWords_eq, ← mat8_posWord8, mat8_mulVec]
  rfl

theorem e0_eq : e0 = vec8 1 := by
  funext i
  fin_cases i <;> rfl

theorem mat8_D1enc : mat8 D1enc = oddD1 := by
  rw [D1enc, mat8_posWord8, mat8_B1enc, mat8_B2enc, oddD1]

theorem mat8_D2enc : mat8 D2enc = oddD2 := by
  rw [D2enc, mat8_posWord8, mat8_B1enc, mat8_B2enc, oddD2]

@[expose] def rTop : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0; 1, 1, 1, 1, 0, 1, 1, 1; 1, 1, 1, 1, 1, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def rBot : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 1;
    1, 1, 1, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0; 1, 1, 1, 1, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem rightInverse_B : (B1 - 1) * rTop + (B2 - 1) * rBot = 1 := by decide

theorem eq_add_of_vec (u : Fin 8 → ZMod 2) :
    u = (B1 - 1).mulVec (rTop.mulVec u) + (B2 - 1).mulVec (rBot.mulVec u) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, rightInverse_B,
    Matrix.one_mulVec]

theorem range_sup_range :
    LinearMap.range (Matrix.mulVecLin (B1 - 1)) ⊔ LinearMap.range (Matrix.mulVecLin (B2 - 1)) =
      ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [eq_add_of_vec u]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

end CFSG.Sporadic.ThSchreier
