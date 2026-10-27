module

public import CFSG.Quasithin.Background.H156Irr
public import CFSG.Quasithin.Background.H153Grp

public section

open scoped Matrix

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H156

abbrev I4 : Type := Fin 2 ⊕ Fin 2

@[expose] def eI : I4 ≃ Fin 4 := finSumFinEquiv

@[expose] def colMatS (cs : List ℕ) : Matrix I4 I4 (ZMod 2) :=
  Matrix.of fun i j => bvec 4 (cs.getD (eI j) 0) (eI i)

@[expose] def J4 : Matrix I4 I4 (ZMod 2) := Matrix.fromBlocks 0 1 (-1) 0

@[expose] def c4 : List ℕ := [7, 1, 13, 15, 4, 0, 0, 0, 0, 0, 0]

theorem c4_len : c4.length = 11 := rfl

theorem c4_surj : ∀ y < 16, ∃ m < 2048, actM c4 m = y := by decide +kernel

theorem c4_ker : ∀ m < 2048, (actM c4 m = 0 ↔ m ∈ combos w0Basis) := by decide +kernel

@[expose] def xC : List ℕ := [13, 3, 12, 8]
@[expose] def xI : List ℕ := [5, 7, 12, 8]
@[expose] def yC : List ℕ := [13, 6, 2, 3]
@[expose] def yI : List ℕ := [12, 4, 6, 11]
@[expose] def oC : List ℕ := [5, 2, 4, 8]

theorem x_type : ∀ m < 2048, actM c4 (act11 lzXArr m) = actM xC (actM c4 m) := by decide +kernel

theorem y_type : ∀ m < 2048, actM c4 (act11 lzYArr m) = actM yC (actM c4 m) := by decide +kernel

theorem o_type : ∀ m < 2048, actM c4 (act11 oddArr m) = actM oC (actM c4 m) := by decide +kernel

theorem t_type : ∀ m < 2048, actM c4 (act11 tArr m) = actM c4 m := by decide +kernel

theorem x_inv1 : colMatS xC * colMatS xI = 1 := by decide +kernel

theorem x_inv2 : colMatS xI * colMatS xC = 1 := by decide +kernel

theorem y_inv1 : colMatS yC * colMatS yI = 1 := by decide +kernel

theorem y_inv2 : colMatS yI * colMatS yC = 1 := by decide +kernel

theorem o_inv : colMatS oC * colMatS oC = 1 := by decide +kernel

theorem x_symp : (colMatS xC)ᵀ * J4 * colMatS xC = J4 := by decide +kernel

theorem y_symp : (colMatS yC)ᵀ * J4 * colMatS yC = J4 := by decide +kernel

theorem o_symp : (colMatS oC)ᵀ * J4 * colMatS oC = J4 := by decide +kernel

@[expose] def trv : List (List ℕ) :=
  [[1, 2, 5, 8], [1, 2, 4, 10], [1, 2, 7, 11], [5, 2, 4, 8], [4, 2, 1, 8], [7, 2, 4, 14],
    [6, 2, 3, 15], [1, 10, 4, 8], [1, 11, 13, 8], [1, 8, 4, 2], [1, 9, 15, 3], [13, 14, 4, 8],
    [12, 15, 9, 8], [15, 12, 4, 6], [14, 13, 11, 7]]

theorem trv_len : ∀ cs ∈ trv, cs.length = 4 := by decide

theorem trv_inv : ∀ cs ∈ trv, colMatS cs * colMatS cs = 1 := by decide +kernel

theorem trv_symp : ∀ cs ∈ trv, (colMatS cs)ᵀ * J4 * colMatS cs = J4 := by decide +kernel

theorem trv_check : ∀ m < 16, m ≠ 0 → ∀ y < 16,
    (spanBits 16 (orbBits 16 trv 1 (1 <<< m))).testBit y = true := by
  decide +kernel

theorem mulVec_cols : ∀ cs ∈ [xC, xI, yC, yI, oC] ++ trv, ∀ q < 16,
    (colMatS cs).mulVec (fun i => bvec 4 q (eI i)) = fun i => bvec 4 (actM cs q) (eI i) := by
  decide +kernel

end CFSG.Quasithin.H153
