
module

public import CFSG.Sporadic.Th.Max3.QuotientBase
public import CFSG.Sporadic.ThSchreier.Enc8
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.Max3.CoreBase
public import CFSG.Sporadic.Th.Max3.RelationsBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

@[expose] def oddWord1 : List ℕ := [1]

@[expose] def oddWord2 : List ℕ :=
  [2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2]

@[expose] def basisPInvEnc : List ℕ := [1, 2, 74, 133, 20, 164, 40, 88]

@[expose] def B1enc : List ℕ := [2, 1, 8, 4, 64, 128, 16, 32]

@[expose] def B2enc : List ℕ := [2, 150, 1, 222, 4, 8, 82, 248]

@[expose] def posWord8 (A B : List ℕ) (w : List ℕ) : List ℕ :=
  w.foldr (fun l acc => mul8 (if l = 1 then A else B) acc) id8

@[expose] def basisWordsL : List (List ℕ) :=
  [[], [1], [2, 1], [1, 2, 1], [2, 1, 2, 1], [1, 2, 1, 2, 1], [2, 2, 1, 2, 1], [1, 2, 2, 1, 2, 1]]

@[expose] def colMat8 (C₁ C₂ : List ℕ) (u : ℕ) : List ℕ :=
  (List.range 8).map fun k => app8 (posWord8 C₁ C₂ (basisWordsL.getD k [])) u

@[expose] def D1enc : List ℕ := posWord8 B1enc B2enc oddWord1

@[expose] def D2enc : List ℕ := posWord8 B1enc B2enc oddWord2

@[expose] def candEnc (C₁ C₂ : List ℕ) (u : ℕ) : List ℕ := mul8 (colMat8 C₁ C₂ u) basisPInvEnc

end CFSG.Sporadic.ThSchreier
