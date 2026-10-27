module

public import CFSG.RankThree.Native.ONSevenArrays

public section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def onThreeY : Array (List ℤ) :=
  #[[-7, 3, -7, -4, 3, 1, -7, -4, -4, -7, -5, 7, 6, -7], [-7, 6, -7, -6]]

@[expose] def onThreeYArrs : Array (Array ℕ) := onThreeY.map onSevenArr

@[expose] def onThreeTreePts : Array ℕ :=
  #[0, 130904, 469, 12244, 235722, 33859, 61825, 124092, 36372, 17840, 143967, 229697, 115059,
    227759, 207472, 32001, 59463, 10440, 41336, 103833, 7934, 16976, 146917, 119089, 188381,
    141000, 192890, 32047, 43557, 48876, 21970, 172705, 191366, 203306, 191659, 189791, 121419,
    7988, 239299, 196540, 138239, 151002, 241901, 120304, 79366, 158814, 190824, 204132, 5189,
    197109, 200619, 42808, 25081, 81531, 243431, 129978, 223749, 173487, 105542, 25035, 3633, 4013,
    86258, 33070, 143251, 121522, 238191, 181054, 171535, 85828, 49943, 78476, 213011, 62816,
    69640, 122244, 24, 16272, 70450, 72061, 36732, 144844, 132909, 10386, 15890, 37065, 50586,
    2095, 21281, 41332]

@[expose] def onThreeTreePar : Array ℕ :=
  #[0, 0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11, 12, 12, 13, 14, 14, 15, 16, 16, 17,
    17, 18, 18, 19, 20, 21, 21, 22, 23, 23, 24, 24, 25, 26, 26, 27, 29, 29, 30, 30, 31, 33, 33, 34,
    35, 37, 38, 39, 39, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 53, 54, 55, 55, 56, 57, 58, 58,
    59, 60, 62, 63, 64, 65, 66, 66, 68, 70, 71, 72, 73, 74, 78]

@[expose] def onThreeTreeGen : Array ℕ :=
  #[0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
    1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1]

@[expose] def onThreeCommOK (x : Array ℕ) : Bool :=
  allBelowN onThreeYArrs.size fun j =>
    peq nPts (pcomp nPts onThreeYArrs[j]! x) (pcomp nPts x onThreeYArrs[j]!)

@[expose] def onThreeTreeOK (ys : Array (Array ℕ)) (pts par gen : Array ℕ) : Bool :=
  pts.size == par.size && pts.size == gen.size && pts[0]! == 0 &&
    allBelowN pts.size fun k => decide (pts[k]! < nPts) && (k == 0 ||
      (decide (par[k]! < k) && decide (gen[k]! < ys.size) &&
        (ys[gen[k]!]!)[pts[par[k]!]!]! == pts[k]!))

@[expose] def onThreeCovers (x pts : Array ℕ) : Bool :=
  (onSevenGood x []).all fun q => pts.contains q

end CFSG.RankThree.Native
