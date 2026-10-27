
module

public import CFSG.Sporadic.Fi23.WideSpec
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.Fi23.Certificate

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev mA : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 253 1 Blueprint.NativeSporadic.Fi23Seed1

noncomputable abbrev mB : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 253 1 Blueprint.NativeSporadic.Fi23Seed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.Fi23Seed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.Fi23Seed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.Fi23Seed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.Fi23Seed2 := seedB_eq'

theorem toVM_matA : toVM matA = CFSG.F3.Native.rowsOf 253 seedA :=
  toVM_rowsOf (by norm_num) seedA

theorem toVM_matB : toVM matB = CFSG.F3.Native.rowsOf 253 seedB :=
  toVM_rowsOf (by norm_num) seedB

theorem toMatW_matA : toMatW 253 matA = mA := by
  rw [toMatW, toVM_matA, toMat_rowsOf, seedA_eq]

theorem toMatW_matB : toMatW 253 matB = mB := by
  rw [toMatW, toVM_matB, toMat_rowsOf, seedB_eq]

theorem matA_size : matA.size = 253 := by
  unfold matA CFSG.F3.Native.rowsOf; simp

theorem matB_size : matB.size = 253 := by
  unfold matB CFSG.F3.Native.rowsOf; simp

theorem rowsWF_matA : RowsWF (toVM matA) := by
  rw [toVM_matA]; exact RowsWF.rowsOf 253 seedA

theorem rowsWF_matB : RowsWF (toVM matB) := by
  rw [toVM_matB]; exact RowsWF.rowsOf 253 seedB

theorem mulW_size (d : ℕ) (X Y : Array W) : (mulW d X Y).size = X.size := by
  unfold mulW; simp

theorem RowsWF.mulW {d : ℕ} {X Y : Array W} (hX : RowsWF (toVM X)) (hY : RowsWF (toVM Y)) :
    RowsWF (toVM (mulW d X Y)) := by
  rw [toVM_mulW]; exact RowsWF.mul _ d hX hY

theorem toMatW_mulW {X Y : Array W} (hXs : X.size = 253) (hX : RowsWF (toVM X))
    (hY : RowsWF (toVM Y)) : toMatW 253 (mulW 253 X Y) = toMatW 253 X * toMatW 253 Y := by
  rw [toMatW, toVM_mulW, toMat_mul (by rw [toVM_size, hXs]) hX hY]

theorem idW_size : (idW 253).size = 253 := by
  unfold idW idM; simp

theorem rowsWF_idW : RowsWF (toVM (idW 253)) := by
  rw [toVM_idW (by norm_num)]; exact RowsWF.idM 253

theorem toMatW_idW : toMatW 253 (idW 253) = 1 := by
  rw [toMatW, toVM_idW (by norm_num), toMat_idM]

theorem powW_size (M : Array W) (e : ℕ) : (powW 253 M e).size = 253 := by
  induction e with
  | zero => exact idW_size
  | succ e ih => rw [powW, mulW_size, ih]

theorem RowsWF.powW {M : Array W} (hM : RowsWF (toVM M)) (e : ℕ) :
    RowsWF (toVM (powW 253 M e)) := by
  induction e with
  | zero => exact rowsWF_idW
  | succ e ih => exact RowsWF.mulW ih hM

theorem toMatW_powW {M : Array W} (hM : RowsWF (toVM M)) (e : ℕ) :
    toMatW 253 (powW 253 M e) = toMatW 253 M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact toMatW_idW
  | succ e ih =>
    rw [Native.powW, toMatW_mulW (powW_size M e) (RowsWF.powW hM e) hM, ih, pow_succ]

@[expose] noncomputable def genMat (x : ℕ) : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  if x = 0 then mA else mB

theorem gens_facts {x : ℕ} (hx : x < 2) :
    (#[matA, matB][x]!).size = 253 ∧ RowsWF (toVM #[matA, matB][x]!) ∧
      toMatW 253 #[matA, matB][x]! = genMat x := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · exact ⟨matA_size, rowsWF_matA, toMatW_matA⟩
  · exact ⟨matB_size, rowsWF_matB, toMatW_matB⟩

theorem toMatW_prodW_aux (word : List ℕ) (hw : ∀ x ∈ word, x < 2) (M : Array W)
    (hMs : M.size = 253) (hM : RowsWF (toVM M)) :
    RowsWF (toVM (word.foldl (fun M x => mulW 253 M #[matA, matB][x]!) M)) ∧
      (word.foldl (fun M x => mulW 253 M #[matA, matB][x]!) M).size = 253 ∧
      toMatW 253 (word.foldl (fun M x => mulW 253 M #[matA, matB][x]!) M) =
        toMatW 253 M * (word.map genMat).prod := by
  induction word generalizing M with
  | nil => exact ⟨hM, hMs, by simp⟩
  | cons x w ih =>
    obtain ⟨-, h2, h3⟩ := gens_facts (hw x List.mem_cons_self)
    have hM' : RowsWF (toVM (mulW 253 M #[matA, matB][x]!)) := RowsWF.mulW hM h2
    have hMs' : (mulW 253 M #[matA, matB][x]!).size = 253 := by rw [mulW_size, hMs]
    obtain ⟨r1, r2, r3⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ hMs' hM'
    refine ⟨r1, r2, ?_⟩
    rw [List.foldl_cons, r3, toMatW_mulW hMs hM h2, h3, List.map_cons, List.prod_cons, mul_assoc]

theorem prodW_facts (word : List ℕ) (hw : ∀ x ∈ word, x < 2) :
    (prodW 253 #[matA, matB] word).size = 253 ∧ RowsWF (toVM (prodW 253 #[matA, matB] word)) ∧
      toMatW 253 (prodW 253 #[matA, matB] word) = (word.map genMat).prod := by
  obtain ⟨h1, h2, h3⟩ := toMatW_prodW_aux word hw (idW 253) idW_size rowsWF_idW
  refine ⟨h2, h1, ?_⟩
  unfold prodW
  rw [h3, toMatW_idW, one_mul]

theorem dWord_lt : ∀ x ∈ dWord, x < 2 := by decide

theorem eWord_lt : ∀ x ∈ eWord, x < 2 := by decide

theorem matBi_size : matBi.size = 253 := by unfold matBi; rw [mulW_size, matB_size]

theorem rowsWF_matBi : RowsWF (toVM matBi) := RowsWF.mulW rowsWF_matB rowsWF_matB

theorem toMatW_matBi : toMatW 253 matBi = mB * mB := by
  unfold matBi; rw [toMatW_mulW matB_size rowsWF_matB rowsWF_matB, toMatW_matB]

noncomputable abbrev mW : Matrix (Fin 253) (Fin 253) (ZMod 3) := (dWord.map genMat).prod

noncomputable abbrev mE : Matrix (Fin 253) (Fin 253) (ZMod 3) := (eWord.map genMat).prod

theorem matD_facts : matD.size = 253 ∧ RowsWF (toVM matD) ∧ toMatW 253 matD = mW ^ 7 := by
  obtain ⟨h1, h2, h3⟩ := prodW_facts dWord dWord_lt
  refine ⟨powW_size _ 7, RowsWF.powW h2 7, ?_⟩
  unfold matD
  rw [toMatW_powW h2, h3]

theorem matE_facts : matE.size = 253 ∧ RowsWF (toVM matE) ∧ toMatW 253 matE = mE :=
  prodW_facts eWord eWord_lt

structure MatrixFacts : Prop where
  A_sq : mA * mA = 1
  B_inv : mB * (mB * mB) = 1
  E_pow : mE ^ 5 = 1
  D_sq : mW ^ 7 * mW ^ 7 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  D_ne : mW ^ 7 ≠ 1

theorem toMatW_ne_of_eqW {X Y : Array W} (hX : X.size = 253) (h : eqW 253 X Y = false)
    (hXc : canonW 253 X = true) (hYc : canonW 253 Y = true) : toMatW 253 X ≠ toMatW 253 Y := by
  intro he
  have := toVM_inj (eq_of_canonM (canonM_of_canonW (by norm_num) (by norm_num) hXc)
    (canonM_of_canonW (by norm_num) (by norm_num) hYc) he)
  subst this
  unfold eqW at h
  simp [hX] at h

theorem toMatW_eq_of_eqW {X Y : Array W} (h : eqW 253 X Y = true) :
    toMatW 253 X = toMatW 253 Y := by
  rw [(eq_of_eqW h).2]

theorem matrixFacts_of (h : matrixChecks = true) : MatrixFacts := by
  unfold matrixChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAc, hBc⟩, hIc⟩, hDc⟩, hA2⟩, hBBi⟩, hE5⟩, hD2⟩, hA1⟩, hB1⟩, hD1⟩ := h
  obtain ⟨hDs, hDw, hDm⟩ := matD_facts
  obtain ⟨hEs, hEw, hEm⟩ := matE_facts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := toMatW_eq_of_eqW hA2
    rwa [toMatW_mulW matA_size rowsWF_matA rowsWF_matA, toMatW_idW, toMatW_matA] at this
  · have := toMatW_eq_of_eqW hBBi
    rwa [toMatW_mulW matB_size rowsWF_matB rowsWF_matBi, toMatW_idW, toMatW_matB,
      toMatW_matBi] at this
  · have := toMatW_eq_of_eqW hE5
    rwa [toMatW_powW hEw, toMatW_idW, hEm] at this
  · have := toMatW_eq_of_eqW hD2
    rwa [toMatW_mulW hDs hDw hDw, toMatW_idW, hDm] at this
  · have := toMatW_ne_of_eqW matA_size hA1 hAc hIc
    rwa [toMatW_idW, toMatW_matA] at this
  · have := toMatW_ne_of_eqW matB_size hB1 hBc hIc
    rwa [toMatW_idW, toMatW_matB] at this
  · have := toMatW_ne_of_eqW hDs hD1 hDc hIc
    rwa [toMatW_idW, hDm] at this

private theorem zmod3_pow3_eq_one : ∀ x : ZMod 3, x ^ 3 = 1 → x = 1 := by decide

private theorem zmod3_pow5_eq_one : ∀ x : ZMod 3, x ^ 5 = 1 → x = 1 := by decide

theorem det_word (w : List ℕ) :
    (w.map genMat).prod.det = (w.map fun x => if x = 0 then mA.det else mB.det).prod := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, List.map_cons, List.prod_cons]
    unfold genMat
    split_ifs <;> rfl

private theorem eWord_det : ∀ x : ZMod 3,
    ((eWord.map fun i => if i = 0 then x else 1).prod) ^ 5 = 1 → x = 1 := by decide

section Facts

variable (hM : MatrixFacts)
include hM

theorem det_mB : mB.det = 1 := by
  apply zmod3_pow3_eq_one
  rw [← Matrix.det_pow, pow_three, hM.B_inv, Matrix.det_one]

theorem det_mA : mA.det = 1 := by
  apply eWord_det
  have h := congrArg Matrix.det hM.E_pow
  rw [Matrix.det_pow, Matrix.det_one, det_word, det_mB hM] at h
  exact h

theorem det_mA_ne_zero : mA.det ≠ 0 := by rw [det_mA hM]; exact one_ne_zero

theorem det_mB_ne_zero : mB.det ≠ 0 := by rw [det_mB hM]; exact one_ne_zero

end Facts

@[expose] noncomputable def orb : WOrbit := orbitData ()

end CFSG.Sporadic.Fi23
