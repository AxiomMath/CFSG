module

public import CFSG.Quasithin.Background.HZCoc24Gen
public import CFSG.Quasithin.Background.HB82Coc24Pred

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

@[expose] def trAArr : Array ℕ :=
  #[1, 21, 9, 4, 19, 5, 6, 15, 18, 12, 22, 20, 16, 8, 14, 10, 0, 11, 23, 7, 13, 2, 3, 17]

@[expose] def trAInv : Array ℕ :=
  #[16, 0, 21, 22, 3, 5, 6, 19, 13, 2, 15, 17, 9, 20, 14, 7, 12, 23, 8, 4, 11, 1, 10, 18]

@[expose] def trBArr : Array ℕ :=
  #[12, 0, 21, 4, 19, 10, 1, 3, 17, 9, 15, 14, 2, 13, 20, 7, 6, 18, 11, 5, 23, 16, 22, 8]

@[expose] def trBInv : Array ℕ :=
  #[1, 6, 12, 7, 3, 19, 16, 15, 23, 9, 5, 18, 0, 13, 11, 10, 21, 8, 17, 4, 14, 2, 22, 20]

@[expose] def trHArr : Array ℕ :=
  #[11, 20, 14, 8, 21, 12, 1, 0, 9, 6, 2, 16, 15, 7, 22, 5, 19, 10, 4, 3, 18, 13, 17, 23]

@[expose] def trHInv : Array ℕ :=
  #[7, 6, 10, 19, 18, 15, 9, 13, 3, 8, 17, 0, 5, 21, 2, 12, 11, 22, 20, 16, 1, 4, 14, 23]

theorem tr_ok : InvPairOK 24 trAArr trAInv = true ∧ InvPairOK 24 trBArr trBInv = true ∧
    InvPairOK 24 trHArr trHInv = true ∧ autArrOK trAArr trAInv = true ∧
    autArrOK trBArr trBInv = true ∧ autArrOK trHArr trHInv = true := by
  decide +kernel

@[expose] def uTBasis : List ℕ := [39, 219, 1108]

theorem uT_combos : ∀ m < 2 ^ 11, m ∈ combos uTBasis ↔ m ∈ uTMasks := by
  decide +kernel

theorem uTBasis_lt : ∀ a ∈ uTBasis, a < 2 ^ 11 := by
  decide +kernel

theorem tr_pres : ∀ m ∈ uTMasks, act11 trAArr m ∈ uTMasks ∧ act11 trBArr m ∈ uTMasks ∧
    act11 trAInv m ∈ uTMasks ∧ act11 trBInv m ∈ uTMasks := by
  decide +kernel

theorem trH_z : act11 trHArr 31 = 1192 := by
  decide +kernel

@[expose] def trW1 : List ℕ := [1592, 702, 82, 1192, 1728, 741, 744]

theorem trW1_eq : w0Basis.map (act11 trHArr) = trW1 := by
  decide +kernel

@[expose] def trLAct (g m : ℕ) : ℕ := act11 (if g = 0 then trAArr else trBArr) m

@[expose] def trCvData : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 10)]

theorem tr_w1_mem : ∀ w ∈ trW1,
    w ∈ combos (trCvData.map fun e => trLAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2) := by
  decide +kernel

theorem tr_notin : act11 trHArr (w0Basis.getD 0 0) ∉ uTMasks := by
  decide +kernel

@[expose] def trC0Arr : Array ℕ := cArr (cArr trAArr trBArr) (cArr trAInv trBInv)

@[expose] def trC1Arr : Array ℕ :=
  cArr (cArr trAArr (cArr trAArr (cArr trBArr trBArr)))
    (cArr trAInv (cArr (cArr trBInv trBInv) trAInv))

@[expose] def trAWord : List ℕ := [0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1]

@[expose] def trBWord : List ℕ := [0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1]

theorem tr_perfect :
    wArr [trC0Arr, trC1Arr] trAWord = trAArr ∧ wArr [trC0Arr, trC1Arr] trBWord = trBArr := by
  decide +kernel

end CFSG.Quasithin.H.Coc24
