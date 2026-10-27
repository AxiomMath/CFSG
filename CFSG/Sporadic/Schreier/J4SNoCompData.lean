
module

public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SFormData

public section

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG.Sporadic.GLQ CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

@[expose] def repWords : Array (List ℤ) := #[[], [1], [2], [1, 2], [2, 2], [2, 1, 2, 2, 2],
  [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2]]

@[expose] def repCounts : Array ℕ := #[2048, 2, 1, 1, 16, 512, 128]

@[expose] def dSets : Array (List ℕ) :=
  #[[], [], [], [], [], [126, 155, 229, 1329, 1359, 1450, 1492], [29]]

@[expose] def kdData : List (ℕ × ℕ × List ℤ) := [
    (126, 5, [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]),
    (155, 5, [2, 1, 2, 1, 2, 2, 1, 2, 2, 1]),
    (229, 5, [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1]),
    (1329, 5, [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1]),
    (1359, 5, [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]),
    (1450, 5, [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1]),
    (1492, 5, [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]),
    (29, 6, [2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1])]
@[expose] def dList : List ℕ := [
    0, 1, 14, 15, 54, 55, 56, 57, 80, 81, 94, 95, 102, 103, 104, 105, 144, 145, 158, 159, 166,
    167, 168, 169, 192, 193, 206, 207, 246, 247, 248, 249, 528, 529, 542, 543, 550, 551, 552,
    553, 576, 577, 590, 591, 630, 631, 632, 633, 640, 641, 654, 655, 694, 695, 696, 697, 720,
    721, 734, 735, 742, 743, 744, 745, 1284, 1285, 1290, 1291, 1330, 1331, 1340, 1341, 1364,
    1365, 1370, 1371, 1378, 1379, 1388, 1389, 1428, 1429, 1434, 1435, 1442, 1443, 1452, 1453,
    1476, 1477, 1482, 1483, 1522, 1523, 1532, 1533, 1812, 1813, 1818, 1819, 1826, 1827, 1836,
    1837, 1860, 1861, 1866, 1867, 1906, 1907, 1916, 1917, 1924, 1925, 1930, 1931, 1970, 1971,
    1980, 1981, 2004, 2005, 2010, 2011, 2018, 2019, 2028, 2029]
@[expose] def chainBase : Array ℕ := #[1, 14, 94, 1290, 158, 166, 528]

@[expose] def chainCnt : Array ℕ := #[1771, 36, 30, 16, 2, 2, 2]

@[expose] def chainWords : Array (Array (List ℕ)) := #[
    #[[], [3, 7, 3], [4, 5, 3], [7], [5, 7], [0, 0, 7], [1, 3], [5, 1, 3], [3, 1], [5, 3, 1],
      [1, 6, 4], [0, 7], [7, 4], [4], [6, 1], [2, 5, 4], [5, 3], [4, 7], [2, 6], [6, 4], [5, 4],
      [0, 6], [1, 0, 6], [1, 5, 4], [3], [7, 3], [4, 1, 6], [1, 6], [6], [7, 6], [0, 6, 1],
      [1, 6, 1], [0, 7, 4], [1], [0, 2, 6], [1, 7]],
    #[[], [0, 5], [0, 0], [5], [0], [0, 0, 5], [0, 5, 2], [5, 0, 0, 2], [0, 3, 0, 1], [0, 2, 0],
      [2, 0, 5], [2], [3, 0, 2, 1], [2, 0, 2], [0, 0, 2], [1, 7, 1], [0, 2, 0, 0], [0, 2, 5],
      [1, 7, 1, 0], [5, 2], [2, 0], [3, 0, 1], [0, 2, 0, 5], [0, 2], [7, 6, 3, 0], [0, 0, 2, 0],
      [5, 0, 2], [6, 0, 3, 6, 0], [2, 5], [2, 0, 0]],
    #[[], [0, 5, 0, 5], [1, 7, 4, 0, 3, 1], [3, 0, 7, 4, 3, 1], [4, 2, 0, 3, 5],
      [3, 5, 2, 7, 2, 0], [3, 0, 7, 1], [1, 7, 0, 0, 3], [2, 1, 0, 4, 0], [1, 4, 3, 1],
      [2, 0, 2, 5, 2, 0], [0, 2, 5, 2, 5], [0, 0, 5, 0], [0, 7, 6, 0, 1], [4, 1, 0, 7, 6, 1],
      [2, 1, 7, 0, 4, 2]],
    #[[], [3, 6, 7, 0, 5, 2]],
    #[[], [7, 0, 7, 0, 7, 0]],
    #[[], [3, 0, 1, 5, 0, 5, 2]]]

@[expose] def unMats : Array (Array ℕ) := Array.ofFn fun j : Fin 11 => (Un j).1

@[expose] def etaV (U : Array (Array ℕ)) (s a : ℕ) : ℕ :=
  (List.finRange 11).foldl (fun acc j => if a.testBit j.val then O.vmul acc U[j.val]! else acc) s

@[expose] def repPair (l : ℕ) : Pair := wordP An Bn repWords[l]!

@[expose] def repVecs : Array ℕ := Array.ofFn fun l : Fin 7 => O.vmul rootBits (repPair l.val).1

@[expose] def conjPair (l : ℕ) (j : Fin 11) : Pair :=
  mulP (mulP (invP (repPair l)) (Un j)) (repPair l)

@[expose] def conjTab : Array (Array (Array ℕ)) :=
  Array.ofFn fun l : Fin 7 => Array.ofFn fun j : Fin 11 => (conjPair l.val j).1

@[expose] def ncommE (U : Array (Array ℕ)) (a : ℕ) (Y : Array ℕ) : Bool :=
  (List.range 112).any fun t =>
    O.vne (O.vmul (etaV U (O.unit t) a) Y) (etaV U (O.vmul (O.unit t) Y) a)

@[expose] def colRows (w : ℕ) : Array ℕ :=
  Array.ofFn fun i : Fin 112 => if w.testBit i then 1 else 0

@[expose] def bilB (u w : ℕ) : Bool := (O.vmul (O.vmul u formRows) (colRows w)).testBit 0

@[noinline, expose] def outsideOK (U : Array (Array ℕ)) (G : Array (Array (Array ℕ))) : Bool :=
  (List.range' 1 6).all fun l => (List.range' 1 2047).all fun a =>
    (dSets[l]!).contains a || (List.range 11).any fun j => ncommE U a (G[l]!)[j]!

@[expose] def swApp (S : Array (Array ℕ)) (w : List ℕ) (a : ℕ) : ℕ :=
  w.foldr (fun i acc => app11 S[i]! acc) a

@[expose] def sTab : Array (Array ℕ) := Array.ofFn fun i : Fin 8 => sCols idx1[i.val]!

end CFSG.Sporadic.J4Schreier.NoComp
