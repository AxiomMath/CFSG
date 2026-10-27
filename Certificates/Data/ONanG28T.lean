module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28TCheck
public import Mathlib

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def tUW : List ℕ := [1, 2, 52, 2]

@[expose] def tZW : List ℕ := [25, 26, 76, 26]

@[expose] def tOW : List ℕ := [9, 65, 33, 89]

@[expose] def tU : Array ℕ := wordCode tUW

@[expose] def tZ : Array ℕ := wordCode tZW

@[expose] def tO : Array ℕ := wordCode tOW

@[expose] def txL : Array (Array ℕ) := t3List tU tZ tO

@[expose] def tzc : Array ℕ := powCode tU 3

@[expose] def tGens : List (Array ℕ × ℕ) := [(tU, 0), (tZ, 0), (tO, 0), (idCode, 1)]

@[expose] def tB1 : ℕ := 55

@[expose] def tB2 : ℕ := 10

@[expose] def tY1 : ℕ := 9

@[expose] def tY2 : ℕ := 0

@[expose] def gW : List (List ℕ) := [
  [41, 89, 1, 49, 44, 92, 52, 1, 42, 4, 2, 41, 2, 1, 41, 2, 1, 52, 41, 4, 2, 49, 1, 4, 52, 41, 4,
    2, 49, 1, 4, 52, 41, 4, 2, 49, 1, 4, 52, 41, 4, 2, 49, 1, 4, 52, 41, 4, 2, 49, 1, 4, 44, 90,
    41, 44],
  [4, 2, 52, 89, 49, 89, 52, 4, 1, 42, 1, 41, 4, 2, 41, 2, 41, 4, 42, 92, 44],
  [1, 41, 1, 41, 1, 41, 1, 41],
  [92, 89, 1, 50, 90, 50, 89, 49, 42, 4, 1, 42, 2, 1, 41, 2, 41, 4, 2, 89, 41, 42, 44]]

end CFSG.AGLEmbedding.KFactProofs.G28
