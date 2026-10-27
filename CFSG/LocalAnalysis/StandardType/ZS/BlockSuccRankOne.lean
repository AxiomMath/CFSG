module

public import TauCeti.LinearAlgebra.Matrix.BlockSucc

public section

namespace Matrix

variable {k : Type*} [CommRing k] {n : ℕ}

theorem blockSucc_one_sub_vecMulVec (ρ κ : Fin n → k) :
    blockSucc (1 - vecMulVec ρ κ) =
      1 - vecMulVec (Fin.snoc ρ 0 : Fin (n + 1) → k) (Fin.snoc κ 0 : Fin (n + 1) → k) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [vecMulVec_apply]
    | cast j => simp [vecMulVec_apply, (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [vecMulVec_apply, (Fin.castSucc_lt_last i).ne]
    | cast j => simp [vecMulVec_apply, one_apply, Fin.castSucc_inj]

end Matrix
