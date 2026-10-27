module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42E49

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Quasithin.H13.D42


@[expose] def powArr (A : Array GF8) : ℕ → Array GF8
  | 0 => oneArr
  | n + 1 => mulArr A (powArr A n)

theorem toMat_powArr (A : Array GF8) (n : ℕ) : toMat (powArr A n) = toMat A ^ n := by
  induction n with
  | zero => rw [powArr, oneArr, toMat_ofMat, pow_zero]
  | succ n ih => rw [powArr, toMat_mulArr, ih, pow_succ']

@[expose] def chunkArr (cs : List (List ℕ)) : Array GF8 :=
  cs.foldr (fun c A => mulArr (wordArr c) A) oneArr

theorem toMat_chunkArr (cs : List (List ℕ)) :
    toMat (chunkArr cs) = (cs.map fun c => toMat (wordArr c)).prod := by
  induction cs with
  | nil => rw [chunkArr, List.foldr_nil, oneArr, toMat_ofMat, List.map_nil, List.prod_nil]
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    show toMat (mulArr (wordArr c) (chunkArr cs)) = _
    exact toMat_mulArr _ _

@[expose] def arrW0 : Array GF8 :=
  (#[1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1] : Array ℕ).map GF8.ofNat'

@[expose] def arrW1 : Array GF8 :=
  (#[0, 5, 0, 4, 7, 1, 2, 7, 0, 5, 0, 4, 7, 3, 2, 2, 2, 2, 5, 1, 2, 4, 0, 0, 2, 3, 5, 2, 0, 1, 6,
    2, 2, 1, 5, 0, 6, 6, 5, 3, 2, 5, 5, 7, 3, 1, 1, 1, 3, 6, 7, 5, 1, 2, 0, 0, 1, 2, 2, 6, 4, 4,
    4, 5] : Array ℕ).map GF8.ofNat'

@[expose] def arrW2 : Array GF8 :=
  (#[0, 3, 0, 2, 5, 1, 6, 5, 0, 3, 0, 2, 5, 7, 6, 6, 6, 6, 3, 1, 6, 2, 0, 0, 6, 7, 3, 6, 0, 1, 4,
    6, 6, 1, 3, 0, 4, 4, 3, 7, 6, 3, 3, 5, 7, 1, 1, 1, 7, 4, 5, 3, 1, 6, 0, 0, 1, 6, 6, 4, 2, 2,
    2, 3] : Array ℕ).map GF8.ofNat'

@[expose] def arrW3 : Array GF8 :=
  (#[3, 2, 1, 7, 0, 2, 4, 6, 7, 3, 2, 0, 3, 6, 2, 4, 3, 4, 1, 0, 5, 4, 5, 2, 0, 2, 6, 0, 0, 0, 0,
    5, 1, 0, 0, 0, 0, 3, 7, 0, 4, 5, 7, 2, 0, 1, 2, 4, 6, 3, 4, 4, 0, 4, 3, 5, 1, 6, 4, 0, 1, 5,
    3, 3] : Array ℕ).map GF8.ofNat'

@[expose] def arrW4 : Array GF8 :=
  (#[0, 7, 0, 6, 3, 1, 4, 3, 0, 7, 0, 6, 3, 5, 4, 4, 4, 4, 7, 1, 4, 6, 0, 0, 4, 5, 7, 4, 0, 1, 2,
    4, 4, 1, 7, 0, 2, 2, 7, 5, 4, 7, 7, 3, 5, 1, 1, 1, 5, 2, 3, 7, 1, 4, 0, 0, 1, 4, 4, 2, 6, 6,
    6, 7] : Array ℕ).map GF8.ofNat'

@[expose] def arrW5 : Array GF8 :=
  (#[5, 7, 6, 0, 7, 4, 6, 2, 5, 5, 4, 3, 0, 7, 4, 6, 7, 6, 1, 5, 0, 6, 2, 4, 1, 0, 0, 0, 0, 7, 5,
    0, 0, 6, 4, 0, 0, 0, 0, 3, 6, 6, 3, 0, 2, 1, 4, 1, 2, 5, 7, 0, 4, 6, 5, 4, 1, 2, 6, 1, 0, 5,
    3, 5] : Array ℕ).map GF8.ofNat'

@[expose] def arrW6 : Array GF8 :=
  (#[7, 3, 2, 0, 3, 6, 2, 4, 7, 7, 6, 5, 0, 3, 6, 2, 3, 2, 1, 7, 0, 2, 4, 6, 1, 0, 0, 0, 0, 3, 7,
    0, 0, 2, 6, 0, 0, 0, 0, 5, 2, 2, 5, 0, 4, 1, 6, 1, 4, 7, 3, 0, 6, 2, 7, 6, 1, 4, 2, 1, 0, 7,
    5, 7] : Array ℕ).map GF8.ofNat'

@[expose] def arrQ1 : Array GF8 :=
  (#[2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 5, 0, 0, 0, 0, 5, 0, 5, 5, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0,
    0, 0] : Array ℕ).map GF8.ofNat'

@[expose] def arrQ2 : Array GF8 :=
  (#[2, 0, 0, 0, 0, 2, 2, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 5, 5, 0, 0, 0,
    0, 5] : Array ℕ).map GF8.ofNat'

@[expose] def arrQ3 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0,
    0, 0] : Array ℕ).map GF8.ofNat'

@[expose] def arrQ4 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0,
    0, 0] : Array ℕ).map GF8.ofNat'

@[expose] def arrQ5 : Array GF8 :=
  (#[2, 0, 0, 0, 0, 0, 2, 0, 0, 5, 5, 0, 0, 0, 0, 5, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 5, 0, 0, 0,
    0, 5] : Array ℕ).map GF8.ofNat'

@[expose] def arrQ6 : Array GF8 :=
  (#[0, 0, 0, 0, 0, 2, 2, 0, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0,
    0, 0, 0, 0, 0, 7, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0,
    0, 5] : Array ℕ).map GF8.ofNat'

@[expose] def lineChunks : Fin 8 → List (List ℕ) :=
  ![[[17, 16, 1, 9, 1, 16, 1, 9, 1]],
    [[1, 16, 2, 1, 9, 1, 16, 17, 16, 1],
      [9, 1, 16, 17, 16, 1, 9, 1, 16, 4],
      [16, 1, 16, 2, 16, 1, 16, 4, 16]],
    [[1, 16, 6, 1, 9, 1, 16, 17, 16, 1],
      [9, 1, 16, 17, 16, 1, 9, 1, 16, 2],
      [16, 1, 16, 6, 16, 1, 16, 2, 16]],
    [[1, 16, 2, 16, 1, 16, 6, 16, 2, 1],
      [9, 1, 16, 17, 16, 1, 9, 1, 16, 17],
      [16, 1, 9, 1, 16, 17, 16, 16, 1, 16],
      [2, 16, 1, 16, 6, 16, 2]],
    [[1, 16, 4, 1, 9, 1, 16, 17, 16, 1],
      [9, 1, 16, 17, 16, 1, 9, 1, 16, 2],
      [16, 1, 16, 4, 16, 1, 16, 2, 16]],
    [[3, 16, 4, 16, 1, 16, 2, 16, 6, 16],
      [1, 9, 1, 16, 17, 16, 1, 9, 1, 16],
      [17, 16, 1, 9, 1, 16, 17, 16, 3, 16],
      [4, 16, 1, 16, 2, 16, 6]],
    [[2, 16, 1, 16, 5, 16, 3, 16, 1, 16],
      [1, 9, 1, 16, 17, 16, 1, 9, 1, 16],
      [17, 16, 1, 9, 1, 16, 17, 16, 2, 16],
      [1, 16, 5, 16, 3, 16, 1]],
    [[17, 16, 1, 9, 1, 16, 1, 9, 1]]]

@[expose] def lineW : Fin 8 → Array GF8 :=
  ![arrW0, arrW1, arrW2, arrW3, arrW4, arrW5, arrW6, arrW0]

@[expose] def lineQ : Fin 8 → Array GF8 :=
  ![e49ArrH, arrQ1, arrQ2, arrQ3, arrQ4, arrQ5, arrQ6, e49ArrZ]

@[expose] def lineExp : Fin 8 → ℕ := ![1, 1, 1, 4, 1, 2, 2, 2]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines
