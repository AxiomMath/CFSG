module

public import CFSG.Quasithin.Background.HZCode22Gen

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

@[expose] def hbAArr : Array ℕ :=
  #[0, 1, 21, 22, 7, 5, 12, 15, 23, 20, 3, 2, 14, 13, 6, 4, 8, 17, 9, 19, 18, 11, 10, 16]

@[expose] def hbAInv : Array ℕ :=
  #[0, 1, 11, 10, 15, 5, 14, 4, 16, 18, 22, 21, 6, 13, 12, 7, 23, 17, 20, 19, 9, 2, 3, 8]

@[expose] def hbBArr : Array ℕ :=
  #[0, 1, 23, 2, 18, 6, 11, 14, 15, 5, 17, 9, 16, 13, 4, 10, 12, 8, 7, 19, 22, 3, 20, 21]

@[expose] def hbBInv : Array ℕ :=
  #[0, 1, 3, 21, 14, 9, 5, 18, 17, 11, 15, 6, 16, 13, 7, 8, 12, 10, 4, 19, 22, 23, 20, 2]

@[expose] def hbHArr : Array ℕ :=
  #[0, 1, 17, 19, 4, 13, 15, 7, 9, 8, 21, 22, 12, 5, 14, 6, 16, 2, 18, 3, 23, 10, 11, 20]

@[expose] def hbHInv : Array ℕ :=
  #[0, 1, 17, 19, 4, 13, 15, 7, 9, 8, 21, 22, 12, 5, 14, 6, 16, 2, 18, 3, 23, 10, 11, 20]

theorem hb_ok : InvPairOK 24 hbAArr hbAInv = true ∧ InvPairOK 24 hbBArr hbBInv = true ∧
    InvPairOK 24 hbHArr hbHInv = true ∧ autArrOK hbAArr hbAInv = true ∧
    autArrOK hbBArr hbBInv = true ∧ autArrOK hbHArr hbHInv = true ∧
    hbAArr[0]! = 0 ∧ hbAArr[1]! = 1 ∧ hbBArr[0]! = 0 ∧ hbBArr[1]! = 1 ∧
    hbHArr[0]! = 0 ∧ hbHArr[1]! = 1 := by
  decide +kernel

@[expose] def hbU0Masks : List ℕ :=
  [0, 19, 194, 209, 354, 369, 416, 435, 513, 530, 707, 720, 867, 880, 929, 946]

@[expose] def hbU0Basis : List ℕ := [19, 194, 354, 513]

theorem hb_combos : ∀ m < 2 ^ 10, m ∈ combos hbU0Basis ↔ m ∈ hbU0Masks := by
  decide +kernel

theorem hbU0Basis_lt : ∀ a ∈ hbU0Basis, a < 2 ^ 10 := by
  decide +kernel

theorem hb_pres : ∀ m ∈ hbU0Masks, actC10 hbAArr m ∈ hbU0Masks ∧
    actC10 hbBArr m ∈ hbU0Masks ∧ actC10 hbAInv m ∈ hbU0Masks ∧ actC10 hbBInv m ∈ hbU0Masks := by
  decide +kernel

theorem hb_ko_pres : ∀ t < 16, ∀ m ∈ hbU0Masks,
    actC10 (cArr hbHArr (cArr (koArr t) hbHInv)) m ∈ hbU0Masks := by
  decide +kernel

theorem hbH_z : actC10 hbHArr 1 = 209 := by
  decide +kernel

@[expose] def hbW1 : List ℕ := [279, 677, 220, 209, 795]

theorem hbW1_eq : w0Basis.map (actC10 hbHArr) = hbW1 := by
  decide +kernel

@[expose] def hbLAct (g m : ℕ) : ℕ := actC10 (if g = 0 then hbAArr else hbBArr) m

@[expose] def hbCvData : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1)]

theorem hb_w1_mem : ∀ w ∈ hbW1,
    w ∈ combos (hbCvData.map fun e => hbLAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2) := by
  decide +kernel

theorem hb_notin : 7 ∈ combos w0Basis ∧ actC10 hbHArr 7 ∉ hbU0Masks := by
  decide +kernel

@[expose] def hbC0Arr : Array ℕ := cArr (cArr hbAArr hbBArr) (cArr hbAInv hbBInv)

@[expose] def hbC1Arr : Array ℕ :=
  cArr (cArr hbAArr (cArr hbAArr hbBArr)) (cArr hbAInv (cArr hbBInv hbAInv))

@[expose] def hbAWord : List ℕ := [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1]

@[expose] def hbBWord : List ℕ := [0, 0, 0, 1, 1, 1, 0, 0, 1]

theorem hb_perfect :
    wArr [hbC0Arr, hbC1Arr] hbAWord = hbAArr ∧ wArr [hbC0Arr, hbC1Arr] hbBWord = hbBArr := by
  decide +kernel

end CFSG.Quasithin.H.Code22
