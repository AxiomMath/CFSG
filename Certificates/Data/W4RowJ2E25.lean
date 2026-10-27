module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2CheckInputs
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.Sporadic.Schreier.RuCore
public import Certificates.Data.W4RowConjInv
public import CFSG.Sporadic.SmallOddCore.J2Data

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Bridge.J2Excl

@[expose] def ep2LineA (n : ℕ) (x y : Array ℕ) : ℕ → Array ℕ
  | 0 => y
  | i + 1 => compA n x (powA n y i)

@[expose] def ep2BaseCheck (n p : ℕ) (x y : Array ℕ) : Bool :=
  eqA n (powA n x p) (idA n) && eqA n (powA n y p) (idA n) && !eqA n x (idA n) &&
    eqA n (compA n x y) (compA n y x) && allLt p (fun j => !eqA n y (powA n x j))

@[expose] def ep2PartCheck (n : ℕ) (x y : Array ℕ) (idx : List (ℕ × ℕ × ℕ)) (ms : List PArr) :
    Bool :=
  idx.length == ms.length && (idx.zip ms).all fun q =>
    eqA n (compA n (compA n q.2.1 (ep2LineA n x y q.1.1)) q.2.2)
      (powA n (ep2LineA n x y q.1.2.1) q.1.2.2)

@[expose] def j2WordP (w : List ℤ) : PArr := pWord 315 [j2A0P, j2A1P] w

@[expose] def j2E25PartIdx : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 2), (0, 3, 2), (1, 0, 2), (1, 3, 1), (2, 5, 2), (2, 4, 2), (3, 0, 2), (3, 1, 1),
   (4, 2, 2), (4, 5, 1), (5, 2, 2), (5, 4, 1)]

@[expose] def j2E25WXStr : String :=
  "2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 \
   2 1 -2 1 -2 1 2 1 2 1 2 2 1 -2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1"

@[expose] def j2E25WX : List ℤ := parseInts j2E25WXStr

@[expose] def j2E25WYStr : String :=
  "-2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 \
   -1 2 -1 -2 -1 -2 -1 2 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 2 1 -2 1 2 1 \
   -2 1 2 1 -2 1 2 1 -2 1 2 1 2 1 2"

@[expose] def j2E25WY : List ℤ := parseInts j2E25WYStr

@[expose] def j2E25WM0Str : String :=
  "2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 \
   -2 -1 2 -1 2 -1 -2 -1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2"

@[expose] def j2E25WM0 : List ℤ := parseInts j2E25WM0Str

@[expose] def j2E25WM1Str : String :=
  "2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 2 \
   -1 -2 -1 2 -1 2"

@[expose] def j2E25WM1 : List ℤ := parseInts j2E25WM1Str

@[expose] def j2E25WM2Str : String :=
  "2 2 1 2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 1 -2 1 2 1 \
   2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 -2 1"

@[expose] def j2E25WM2 : List ℤ := parseInts j2E25WM2Str

@[expose] def j2E25WM3Str : String :=
  "-2 -1 2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 \
   2 2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 2 2"

@[expose] def j2E25WM3 : List ℤ := parseInts j2E25WM3Str

@[expose] def j2E25WM4Str : String :=
  "-2 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -2 1 2 1 -2 1 -2 1 2 1 -2 1 2"

@[expose] def j2E25WM4 : List ℤ := parseInts j2E25WM4Str

@[expose] def j2E25WM5Str : String :=
  "2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 2 \
   -1 -2 -1 2 -1 2"

@[expose] def j2E25WM5 : List ℤ := parseInts j2E25WM5Str

@[expose] def j2E25WM6Str : String :=
  "-2 -1 2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 \
   2 2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 2 2"

@[expose] def j2E25WM6 : List ℤ := parseInts j2E25WM6Str

@[expose] def j2E25WM7Str : String :=
  "-2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -2 1 2 1 -2 1 2 1 2 -1 -2 -1 2 -1 2 -1 \
   -2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 \
   2"

@[expose] def j2E25WM7 : List ℤ := parseInts j2E25WM7Str

@[expose] def j2E25WM8Str : String :=
  "-2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 2 1 2 1 \
   -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2"

@[expose] def j2E25WM8 : List ℤ := parseInts j2E25WM8Str

@[expose] def j2E25WM9Str : String :=
  "2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 \
   -1 2 -1 -2 -1 -2 -2 1 2 1 -2 1 2 1 -2 1 2 1 2 1 2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 -2 1 2 1 \
   2 1 -2 1 2"

@[expose] def j2E25WM9 : List ℤ := parseInts j2E25WM9Str

@[expose] def j2E25WM10Str : String :=
  "-2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 \
   -1 2 -1 -2 -1 -2 -1 2 -1 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1"

@[expose] def j2E25WM10 : List ℤ := parseInts j2E25WM10Str

@[expose] def j2E25WM11Str : String :=
  "-1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 -2 -2 1 -2 1 -2 1 2 1 2 1 -2 1 2 1 \
   -2 1 2 1 2 1 -2 1 -2 1 2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 -2 1"

@[expose] def j2E25WM11 : List ℤ := parseInts j2E25WM11Str

@[expose] def j2E25WHAStr : String :=
  "2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 \
   -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 1 2"

@[expose] def j2E25WHA : List ℤ := parseInts j2E25WHAStr

@[expose] def j2E25WHBStr : String :=
  "2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 2 -1 \
   -2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -2 1 -2 1 2 1 2 1 -2 1 2 1 -2 1 2 \
   1 2 1 -2 1 -2 1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2"

@[expose] def j2E25WHB : List ℤ := parseInts j2E25WHBStr

@[expose] def j2E25WMs : List (List ℤ) :=
  [j2E25WM0, j2E25WM1, j2E25WM2, j2E25WM3, j2E25WM4, j2E25WM5, j2E25WM6, j2E25WM7, j2E25WM8,
   j2E25WM9, j2E25WM10, j2E25WM11]

@[expose] def j2Outer3Words : List (List ℤ) := [[], [-1, 2], [2, 2]]

@[expose] def j2Outer3Prog : List (ℤ × ℤ) :=
  [(1, 3), (4, 1), (5, 2), (6, 1), (7, 2), (8, 3), (9, 2), (10, 1), (11, 3), (12, 2), (13, 1),
   (14, 2), (15, 3), (16, 2), (17, 3), (3, 1), (19, 2), (20, 1), (21, 3), (22, 1), (23, 2),
   (24, 1), (25, 3), (26, 2), (27, 1), (28, 2)]

@[expose] def j2E25Check : Bool :=
  ep2BaseCheck 315 5 (j2WordP j2E25WX).1 (j2WordP j2E25WY).1 &&
    ep2PartCheck 315 (j2WordP j2E25WX).1 (j2WordP j2E25WY).1 j2E25PartIdx
      (j2E25WMs.map j2WordP) &&
    conjInvCheck 315 (j2TP 17) (j2WordP j2E25WHB) (j2WordP j2E25WX) &&
    conjInvCheck 315 (j2TP 31) (j2WordP j2E25WHA) (j2WordP j2E25WX) &&
    threeConjCheck 315 [j2A0P, j2A1P] (j2TP 9) j2Outer3Words j2Outer3Prog [j2A0A, j2A1A]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
