
module

public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.Fi24Core

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rowW_rowsOfSeed (d : ℕ) (s : String) {i : ℕ} (hi : i < d) :
    rowW (rowsOfSeed d s) i =
      ofTrits d fun j => (CFSG.F3.Native.decodeEntries s).toArray[i * d + j]?.getD 0 := by
  unfold rowsOfSeed
  rw [rowW_ofFn, dite_eq_left hi]

theorem rowsWF_rowsOfSeed (s : String) : RowsWF (rowsOfSeed 781 s) := by
  intro x hx
  unfold rowsOfSeed at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by norm_num) _

theorem rowsOfSeed_size (s : String) : (rowsOfSeed 781 s).size = 781 := by
  unfold rowsOfSeed; simp

theorem matW_rowsOfSeed (s : String) :
    matW 781 781 (rowsOfSeed 781 s) = Blueprint.NativeSporadic.decode 3 781 1 s := by
  ext i j
  rw [matW_apply, rowW_rowsOfSeed 781 s i.isLt, ofTrits_val (by norm_num), ite_eq_left j.isLt,
    CFSG.F3.Native.decode_apply_eq_decodeEntries, List.getElem?_toArray]

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.Fi24primeSeed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.Fi24primeSeed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.Fi24primeSeed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.Fi24primeSeed2 := seedB_eq'

theorem matW_matA : matW 781 781 matA = mA := by
  unfold matA; rw [matW_rowsOfSeed, seedA_eq]

theorem matW_matB : matW 781 781 matB = mB := by
  unfold matB; rw [matW_rowsOfSeed, seedB_eq]

theorem matA_size : matA.size = 781 := rowsOfSeed_size _

theorem matB_size : matB.size = 781 := rowsOfSeed_size _

theorem rowsWF_matA : RowsWF matA := rowsWF_rowsOfSeed _

theorem rowsWF_matB : RowsWF matB := rowsWF_rowsOfSeed _

theorem matW_matAT : matW 781 781 matAT = mAᵀ := by
  unfold matAT; rw [matW_transposeW (by norm_num) rowsWF_matA, matW_matA]

theorem matW_matBT : matW 781 781 matBT = mBᵀ := by
  unfold matBT; rw [matW_transposeW (by norm_num) rowsWF_matB, matW_matB]

theorem rowsWF_matAT : RowsWF matAT := RowsWF.transposeW (by norm_num) _ _

theorem rowsWF_matBT : RowsWF matBT := RowsWF.transposeW (by norm_num) _ _

theorem matAT_size : matAT.size = 781 := transposeW_size _ _ _

theorem matBT_size : matBT.size = 781 := transposeW_size _ _ _

theorem rowsWF_matF_form : RowsWF matF := by
  intro x hx
  unfold matF at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by norm_num) _

theorem matF_size_form : matF.size = 781 := by
  unfold matF; simp

structure MatrixFacts : Prop where
  A_sq : mA * mA = 1
  B_cube : mB * (mB * mB) = 1
  AB_pow : (mA * mB) ^ 29 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  AB_ne : mA * mB ≠ 1
  A_form : mAᵀ * mF * mA = mF
  B_form : mBᵀ * mF * mB = mF
  F_wf : RowsWF matF
  F_size : matF.size = 781

theorem matW_mulW' {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) (hYs : Y.size = 781) :
    matW 781 781 (mulW X Y) = matW 781 781 X * matW 781 781 Y :=
  matW_mulW (by norm_num) hX hY (by omega)

theorem matW_ne_of_eqRows {X : Array W} (hX : canonRows 781 X = true)
    (h : eqRows 781 X (idW 781) = false) : matW 781 781 X ≠ 1 := by
  intro he
  rw [← matW_idW (by norm_num)] at he
  have e := eq_of_matW_eq hX canonRows_idW he
  have hs : X.size = 781 := (canonRows_spec hX).1
  have : eqRows 781 X (idW 781) = true := by
    unfold eqRows
    rw [e, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨idW_size 781, rfl⟩
  rw [this] at h
  exact absurd h (by decide)

theorem matrixFacts_of (h : matrixChecks () = true) : MatrixFacts := by
  unfold matrixChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAc, hBc⟩, hFc⟩, hA2⟩, hB3⟩, hAB⟩, hA1⟩, hB1⟩, hAB1⟩, hAF⟩, hBF⟩ := h
  have hFw := RowsWF.of_canonRows hFc
  have hFs := (canonRows_spec hFc).1
  have hAB_w : RowsWF (mulW matA matB) := RowsWF.mulW rowsWF_matA rowsWF_matB
  have hmAB : matW 781 781 (mulW matA matB) = mA * mB := by
    rw [matW_mulW' rowsWF_matA rowsWF_matB matB_size, matW_matA, matW_matB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hFw, hFs⟩
  · have := congrArg (matW 781 781) (eq_of_eqRows hA2).2
    rwa [matW_mulW' rowsWF_matA rowsWF_matA matA_size, matW_idW (by norm_num), matW_matA] at this
  · have := congrArg (matW 781 781) (eq_of_eqRows hB3).2
    rwa [matW_mulW' rowsWF_matB (RowsWF.mulW rowsWF_matB rowsWF_matB)
        (by rw [mulW_size, matB_size]),
      matW_mulW' rowsWF_matB rowsWF_matB matB_size, matW_idW (by norm_num), matW_matB] at this
  · have := congrArg (matW 781 781) (eq_of_eqRows hAB).2
    rwa [matW_powW (by norm_num) hAB_w (by rw [mulW_size, matA_size]), hmAB,
      matW_idW (by norm_num)] at this
  · have := matW_ne_of_eqRows hAc hA1
    rwa [matW_matA] at this
  · have := matW_ne_of_eqRows hBc hB1
    rwa [matW_matB] at this
  · have := matW_ne_of_eqRows (canonRows_mulW hAc hBc) hAB1
    rwa [hmAB] at this
  · have := congrArg (matW 781 781) (eq_of_eqRows hAF).2
    rwa [matW_mulW' (RowsWF.mulW rowsWF_matAT hFw) rowsWF_matA matA_size,
      matW_mulW' rowsWF_matAT hFw hFs, matW_matAT, matW_matA] at this
  · have := congrArg (matW 781 781) (eq_of_eqRows hBF).2
    rwa [matW_mulW' (RowsWF.mulW rowsWF_matBT hFw) rowsWF_matB matB_size,
      matW_mulW' rowsWF_matBT hFw hFs, matW_matBT, matW_matB] at this

private theorem zmod3_pow3_eq_one : ∀ x : ZMod 3, x ^ 3 = 1 → x = 1 := by decide

private theorem zmod3_pow29_eq_one : ∀ x : ZMod 3, x ^ 29 = 1 → x = 1 := by decide

end CFSG.Sporadic.Fi24
