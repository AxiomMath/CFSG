module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.RankThree.PartOne.CTP.D4Two

open Matrix CFSG.ClassicalGroups.Orthogonal

@[expose] def K2 : Type := ZMod 2

instance : Field K2 := inferInstanceAs (Field (ZMod 2))
instance : DecidableEq K2 := inferInstanceAs (DecidableEq (ZMod 2))
instance : Fintype K2 := inferInstanceAs (Fintype (ZMod 2))
instance : CharP K2 2 := inferInstanceAs (CharP (ZMod 2) 2)

abbrev Idx : Type := Fin 4 ⊕ Fin 4

abbrev Vec : Type := Idx → K2

@[expose] def bitMat (cols : Fin 8 → ℕ) : Matrix Idx Idx (K2) :=
  fun r c => if (cols (finSumFinEquiv c)).testBit (finSumFinEquiv r) then 1 else 0

@[expose] def bitVec (n : ℕ) : Vec :=
  fun r => if n.testBit (finSumFinEquiv r) then 1 else 0

@[expose] def qf (v : Vec) : K2 := ∑ i : Fin 4, v (.inl i) * v (.inr i)

@[expose] def pf (v w : Vec) : K2 :=
  ∑ i : Fin 4, (v (.inl i) * w (.inr i) + w (.inl i) * v (.inr i))

@[expose] def IsIsom (M : Matrix Idx Idx (K2)) : Prop :=
  (∀ i : Idx, qf (M.mulVec (Pi.single i 1)) = qf (Pi.single i 1)) ∧
    ∀ i j : Idx, pf (M.mulVec (Pi.single i 1)) (M.mulVec (Pi.single j 1)) =
      pf (Pi.single i 1) (Pi.single j 1)

instance (M : Matrix Idx Idx (K2)) : Decidable (IsIsom M) := by
  unfold IsIsom
  infer_instance

@[expose] def mX1 : Matrix Idx Idx (K2) := bitMat ![204, 18, 210, 206, 111, 153, 150, 255]

@[expose] def mX2 : Matrix Idx Idx (K2) := bitMat ![159, 146, 120, 6, 16, 24, 4, 40]

@[expose] def mY1 : Matrix Idx Idx (K2) := bitMat ![95, 170, 175, 15, 161, 111, 56, 115]

@[expose] def mY2 : Matrix Idx Idx (K2) := bitMat ![6, 111, 14, 123, 213, 11, 237, 7]

@[expose] def mY1i : Matrix Idx Idx (K2) := bitMat ![28, 111, 26, 97, 219, 250, 210, 246]

@[expose] def mY2i : Matrix Idx Idx (K2) := bitMat ![129, 164, 165, 5, 175, 250, 125, 230]

@[expose] def mX (i j : ℕ) : Matrix Idx Idx (K2) := mX1 ^ i * mX2 ^ j

theorem isIsom_mX1 : IsIsom mX1 := by decide +kernel
theorem isIsom_mX2 : IsIsom mX2 := by decide +kernel
theorem isIsom_mY1 : IsIsom mY1 := by decide +kernel
theorem isIsom_mY2 : IsIsom mY2 := by decide +kernel
theorem isIsom_mY1i : IsIsom mY1i := by decide +kernel
theorem isIsom_mY2i : IsIsom mY2i := by decide +kernel

theorem mX1_pow : mX1 ^ 5 = 1 := by decide +kernel
theorem mX2_pow : mX2 ^ 5 = 1 := by decide +kernel
theorem mY1_pow : mY1 ^ 15 = 1 := by decide +kernel
theorem mY2_pow : mY2 ^ 15 = 1 := by decide +kernel
theorem mY1i_pow : mY1i ^ 15 = 1 := by decide +kernel
theorem mY2i_pow : mY2i ^ 15 = 1 := by decide +kernel

theorem mY1_mul_inv : mY1 * mY1i = 1 := by decide +kernel
theorem mY1_inv_mul : mY1i * mY1 = 1 := by decide +kernel
theorem mY2_mul_inv : mY2 * mY2i = 1 := by decide +kernel
theorem mY2_inv_mul : mY2i * mY2 = 1 := by decide +kernel

theorem mX_comm : mX1 * mX2 = mX2 * mX1 := by decide +kernel

theorem mX_inj : ∀ i j : ZMod 5, mX i.val j.val = 1 → i = 0 ∧ j = 0 := by decide +kernel

theorem mY1_comm : mY1 * mX 1 3 = mX 1 3 * mY1 := by decide +kernel
theorem mY1i_comm : mY1i * mX 1 3 = mX 1 3 * mY1i := by decide +kernel
theorem mY2_comm : mY2 * mX 1 2 = mX 1 2 * mY2 := by decide +kernel
theorem mY2i_comm : mY2i * mX 1 2 = mX 1 2 * mY2i := by decide +kernel

theorem mX2_fix_11 : mX2.mulVec (bitVec 11) = bitVec 11 := by decide +kernel
theorem mX2_fix_116 : mX2.mulVec (bitVec 116) = bitVec 116 := by decide +kernel
theorem mX2_fix_162 : mX2.mulVec (bitVec 162) = bitVec 162 := by decide +kernel
theorem mX2_fix_111 : mX2.mulVec (bitVec 111) = bitVec 111 := by decide +kernel
theorem mX2_fix_169 : mX2.mulVec (bitVec 169) = bitVec 169 := by decide +kernel
theorem mX2_fix_27 : mX2.mulVec (bitVec 27) = bitVec 27 := by decide +kernel
theorem mX2_fix_214 : mX2.mulVec (bitVec 214) = bitVec 214 := by decide +kernel

theorem word3 : mY1.mulVec (mY2.mulVec (bitVec 11)) = bitVec 11 ∧
    mY1.mulVec (mY2.mulVec (bitVec 116)) = bitVec 49 := by decide +kernel
theorem word4 : mY2.mulVec (mY1i.mulVec (bitVec 111)) = bitVec 11 ∧
    mY2.mulVec (mY1i.mulVec (bitVec 169)) = bitVec 53 := by decide +kernel
theorem word5 : mY1i.mulVec (mY2.mulVec (bitVec 111)) = bitVec 11 ∧
    mY1i.mulVec (mY2.mulVec (bitVec 27)) = bitVec 77 := by decide +kernel
theorem word6 : mY2i.mulVec (mY1i.mulVec (bitVec 11)) = bitVec 11 ∧
    mY2i.mulVec (mY1i.mulVec (bitVec 214)) = bitVec 71 := by decide +kernel

theorem qf_e : qf (bitVec 11) = 0 := by decide +kernel
theorem qf_f : qf (bitVec 250) = 0 := by decide +kernel
theorem pf_ef : pf (bitVec 11) (bitVec 250) = 1 := by decide +kernel
theorem mY1_e : mY1.mulVec (bitVec 11) = bitVec 250 := by decide +kernel
theorem e_ne_zero : bitVec 11 ≠ 0 := by decide +kernel

theorem pf_e_w :
    pf (bitVec 11) (bitVec 116) = 0 ∧ pf (bitVec 11) (bitVec 162) = 0 ∧
      pf (bitVec 11) (bitVec 49) = 0 ∧ pf (bitVec 11) (bitVec 53) = 0 ∧
      pf (bitVec 11) (bitVec 77) = 0 ∧ pf (bitVec 11) (bitVec 71) = 0 := by decide +kernel

@[expose] def spanCols : Matrix Idx (Fin 7) (K2) :=
  fun r j => if (![11, 116, 162, 49, 53, 77, 71] j).testBit (finSumFinEquiv r) then 1 else 0

@[expose] def spanCoords : Matrix (Fin 7) Idx (K2) :=
  fun j c => if (![81, 202, 48, 158, 244, 233, 211] j).testBit (finSumFinEquiv c) then 1 else 0

theorem span_identity :
    spanCols * spanCoords =
      1 + Matrix.vecMulVec (bitVec 250) (fun c => pf (bitVec 11) (Pi.single c 1)) := by
  decide +kernel

end CFSG.RankThree.PartOne.CTP.D4Two
