module

public import CFSG.Monster.B.Final.Basic
public import CFSG.Monster.B.Max2.Facts
public import Certificates.Certificate3109
public import CFSG.Monster.B.Cbar.SimpleBase

public section

namespace CFSG.Monster.B

open Matrix MulOpposite Bin CFSG.Blueprint

@[expose] noncomputable def wordS (g : ℕ → Cbar) (w : List ℕ) : Sbp :=
  (w.map fun j => op (g j)).prod

section Beta

variable (β : Cbar →* GL (Fin 4370) (ZMod 2)) (g : ℕ → Cbar)
  (hg : ∀ j < 26, ((betaRow β (op (g j)) : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ) :
    Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = Qn j)

include hg in
theorem betaRow_wordS (w : List ℕ) (hw : ∀ j ∈ w, j < 26) :
    ((betaRow β (wordS g w) : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = wordQ Qn w := by
  induction w with
  | nil => simp [wordS, wordQ]
  | cons j w ih =>
    rw [wordS, List.map_cons, List.prod_cons, map_mul, Units.val_mul, ← wordS,
      ih (fun j' h => hw j' (List.mem_cons_of_mem _ h)), hg j (hw j (List.mem_cons_self ..))]
    simp [wordQ]

@[expose] noncomputable def eS (i : ℕ) : Sbp :=
  (wordS g (basisWord.take (basisLens.getD i 0)))⁻¹ * op (g 0) *
    wordS g (basisWord.take (basisLens.getD i 0))

theorem basisWord_lt : ∀ j ∈ basisWord, j < 26 := by
  intro j hj
  simp only [basisWord, List.mem_cons, List.mem_nil_iff, or_false] at hj
  omega

theorem parityWord_lt : ∀ j ∈ parityWord24, j < 26 := by
  intro j hj
  simp only [parityWord24, List.mem_cons, List.mem_nil_iff, or_false] at hj
  omega

include hg in
theorem betaRow_eS (i : ℕ) :
    ((betaRow β (eS g i) : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = Em Qn i := by
  rw [eS, map_mul, map_mul, Units.val_mul, Units.val_mul, map_inv, Matrix.coe_units_inv,
    betaRow_wordS β g hg _ (fun j h => basisWord_lt j (List.mem_of_mem_take h)), hg 0 (by norm_num)]
  rfl

@[expose] noncomputable def WS : Sbp := wordS g parityWord24

include hg in
theorem betaRow_WS :
    ((betaRow β (WS g) : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = wordQ Qn parityWord24 :=
  betaRow_wordS β g hg parityWord24 parityWord_lt

@[expose] noncomputable def xS : Sbp := (op (g 0) * ((op (g 1))⁻¹ * op (g 0) * op (g 1))) ^ 2

include hg in
theorem betaRow_xS :
    ((betaRow β (xS g) : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = Xm Qn := by
  rw [xS, map_pow, Units.val_pow_eq_pow_val, map_mul, map_mul, map_mul, map_inv, Units.val_mul,
    Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hg 0 (by norm_num), hg 1 (by norm_num)]
  rfl

end Beta

@[expose] noncomputable def cB :
    NativeSporadic.B := progRegs bA₁ bA₂ 1

@[expose] noncomputable def dB :
    NativeSporadic.B := progRegs bA₁ bA₂ 2

@[expose] noncomputable def DB : NativeSporadic.B := dB ^ 24

@[expose] noncomputable def W'B :
    NativeSporadic.B := bA₂⁻¹ * DB * bA₂

theorem bMat_cB : bMat cB = cMat := map_progRegs bMat bA₁ bA₂ 1

theorem bMat_dB : bMat dB = dMat := map_progRegs bMat bA₁ bA₂ 2

theorem bMat_DB : bMat DB = dMat ^ 24 := by rw [DB, map_pow, bMat_dB]

theorem bMat_W'B : bMat W'B = W'm dMat genA₂ := by
  rw [W'B, map_mul, map_mul, bMat_bA₂_inv, bMat_bA₂, bMat_DB, W'm, sq]

end CFSG.Monster.B
