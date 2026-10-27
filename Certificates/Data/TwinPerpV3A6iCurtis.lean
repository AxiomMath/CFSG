module

public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.ClassicalInvolution.Phan.Phan3AData
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def curtisLetterA (i : ℕ) : ℕ := 4 * i

@[expose] def curtisLetterB (i : ℕ) : ℕ := 4 * i + 2

@[expose] def curtisInvLetter (k : ℕ) : ℕ := if k % 2 = 0 then k + 1 else k - 1

@[expose] def curtisInvWord (w : List ℕ) : List ℕ := (w.map curtisInvLetter).reverse

@[expose] def curtisPowWord (w : List ℕ) (k : ℕ) : List ℕ := (List.replicate k w).flatten

@[expose] def curtisCommWord (u v : List ℕ) : List ℕ := u ++ v ++ curtisInvWord u ++ curtisInvWord v

@[expose] def curtisNWord (i : ℕ) : List ℕ := [curtisLetterA i, curtisLetterB i, curtisLetterA i]

@[expose] def curtisNRel (c d i j : ℕ) : List ℕ :=
  curtisNWord c ++ [curtisLetterA d] ++ curtisNWord c ++
    curtisInvWord (curtisPowWord [curtisLetterA i, curtisLetterA j] 2)

@[expose] def curtisRankOne (i : ℕ) : List (List ℕ) :=
  [[curtisLetterA i, curtisLetterA i], [curtisLetterB i, curtisLetterB i],
    curtisPowWord [curtisLetterA i, curtisLetterB i] 3]

@[expose] def curtisNonAdj (i j : ℕ) : List (List ℕ) :=
  [curtisCommWord [curtisLetterA i] [curtisLetterA j],
    curtisCommWord [curtisLetterA i] [curtisLetterB j],
    curtisCommWord [curtisLetterB i] [curtisLetterA j],
    curtisCommWord [curtisLetterB i] [curtisLetterB j]]

@[expose] def curtisAdj (i j : ℕ) : List (List ℕ) :=
  [curtisCommWord [curtisLetterA i] [curtisLetterB j],
    curtisCommWord [curtisLetterB i] [curtisLetterA j],
    curtisPowWord [curtisLetterA i, curtisLetterA j] 4,
    curtisPowWord [curtisLetterB i, curtisLetterB j] 4,
    curtisNRel i j i j, curtisNRel j i i j]

@[expose] def curtisRels : List (List ℕ) :=
  (List.range 4).flatMap curtisRankOne ++
    [(0, 2), (0, 3), (2, 3)].flatMap (fun p => curtisNonAdj p.1 p.2) ++
    [(0, 1), (2, 1), (3, 1)].flatMap (fun p => curtisAdj p.1 p.2)

@[expose] def curtisPG : List (List (Fin 8 × Bool)) := curtisRels.map (decodeWord 8)

@[expose] def curtisIndexCheck (_ : Unit := ()) : Bool :=
  subsetCheckCC curtisPG [2, 3, 4, 5, 6, 7] 30000 8640

@[expose] def curtisSub : List (List (Fin (subsetOf 8 [2, 3, 4, 5, 6, 7]).length × Bool)) :=
  restrictWords (subsetOf 8 [2, 3, 4, 5, 6, 7]) curtisPG

@[expose] def curtisSubIndexCheck (_ : Unit := ()) : Bool :=
  subsetCheckCC curtisSub [2, 3, 4, 5] 20000 560

@[expose] def curtisSubSub :
    List (List (Fin (subsetOf (subsetOf 8 [2, 3, 4, 5, 6, 7]).length [2, 3, 4, 5]).length × Bool)) :=
  restrictWords (subsetOf (subsetOf 8 [2, 3, 4, 5, 6, 7]).length [2, 3, 4, 5]) curtisSub

@[expose] def curtisSubSubCheck (_ : Unit := ()) : Bool :=
  subsetCheckCC curtisSubSub [] 2000 36

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
