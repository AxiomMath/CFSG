module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheckInputs
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.Sporadic.Schreier.RuCore
public import Certificates.Data.W4RowConjInv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Sporadic.Schreier
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab

@[expose] def e9PackCheck (n : ℕ) (x y m₁ m₂ m₃ k : PArr) : Bool :=
  let e := idA n
  let b := compA n x.1 (compA n (compA n k.1 x.1) k.2)
  eqA n (powA n x.1 3) e && eqA n (powA n y.1 3) e && !eqA n x.1 e &&
    eqA n (compA n x.1 y.1) (compA n y.1 x.1) && allLt 3 (fun j => !eqA n y.1 (powA n x.1 j)) &&
    eqA n (compA n (compA n m₁.1 x.1) m₁.2) y.1 &&
    eqA n (compA n (compA n m₂.1 x.1) m₂.2) (compA n x.1 y.1) &&
    eqA n (compA n (compA n m₃.1 x.1) m₃.2) (compA n x.1 (powA n y.1 2)) &&
    eqA n (powA n b 5) e && !eqA n b e

@[expose] def hsE9WXStr : String :=
  "-2 -2 1 2 2 1 -2 -2 1 2 2 2 1 2 1 -2 1 -2 1 2 2 1 2 2 1 2 1 -2 1 -2 -2 1 2 1 2 1 -2 -2 1 2 1 \
   -2 1 2"

@[expose] def hsE9WX : List ℤ := parseInts hsE9WXStr

@[expose] def hsE9WYStr : String :=
  "-2 -2 -1 2 2 -1 -2 -1 2 2 -1 2 2 -1 -2 -2 -2 -1 2 2 2 -1 2 -1 -2 -1 2 -1 -2 -2 -1 -2 -1 -2 \
   -2 -1 2 -1 -2 -1 -2 -2 -1 -2 -1"

@[expose] def hsE9WY : List ℤ := parseInts hsE9WYStr

@[expose] def hsE9WM1Str : String :=
  "2 -1 -2 -1 -2 -2 -1 -2 -2 -2 1 2 1 -2 1 2 1 2 2 1 2 1 -2 -2 1 -2 -2 1 2 1 -2 -2 1 2 -1 -2 -2 \
   -1 2 2 -1 -2 -2 -1 2 2 -1"

@[expose] def hsE9WM1 : List ℤ := parseInts hsE9WM1Str

@[expose] def hsE9WM2Str : String :=
  "-1 -2 -1 -2 -1 2 2 -1 -2 -1 2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 -2 -1 -2 -2 -1 -2 -2 -1 2 \
   -1 -2 -2 -1 2 -1 -2 -2 -2 -1 2 2"

@[expose] def hsE9WM2 : List ℤ := parseInts hsE9WM2Str

@[expose] def hsE9WM3Str : String :=
  "-2 -2 1 2 2 1 2 1 2 2 1 -2 -2 1 2 2 1 2 -1 -2 -1 -2 -1 2 2 -1 2 2 -1 2 -1 -2 -1 -2 -2 -1 2 2 \
   -1"

@[expose] def hsE9WM3 : List ℤ := parseInts hsE9WM3Str

@[expose] def hsE9WKStr : String :=
  "-1 -2 -1 -2 -1 -2 -2 -1 2 2 2 1 -2 -2 1 -2 1 -2 1 -2 -2 1 2 2 1 -2 -2 1 2 1 -2 -1 2 2 -1 -2 \
   -2 -1 2 2 -1"

@[expose] def hsE9WK : List ℤ := parseInts hsE9WKStr

@[expose] def hsE9WH5Str : String :=
  "-2 -2 -1 2 2 -1 -2 -2 -1 2 2 -1 -2 -2 -1 2 2 2 1 2 1 -2 -2 1 2 1 2 1 2 1 2 -1 2 2 -1 -2 -2 \
   -1 2 -1 2 -1 2 2 1 -2 -2 1 -2 1 2 2 1 2 1 2 1 2"

@[expose] def hsE9WH5 : List ℤ := parseInts hsE9WH5Str

@[expose] def hsE9WH12Str : String :=
  "-2 -2 -1 2 2 -1 -2 -2 -1 2 2 -1 -2 -2 -1 2 2 2 1 2 1 2 1 2 1 2 1 -2 -1 -2 -1 2 -1 -2 -2 -1 2 \
   -1 -2 -1 -2 -2 -2 1 2 -1 2 -1 -2 -2 -1 -2 -1 -2 -2"

@[expose] def hsE9WH12 : List ℤ := parseInts hsE9WH12Str

@[expose] def hsE9WH21Str : String :=
  "-2 -1 -2 -1 -2 -1 -2 -1 -2 -1 -2 -2 -1 2 -1 -2 1 -2 1 2 1 2 1 -2 -2 1 2 2 1 2 1 -2 -2 1 -2 1 \
   -2 -1 2 2"

@[expose] def hsE9WH21 : List ℤ := parseInts hsE9WH21Str

@[expose] def hsE9WH34Str : String :=
  "-1 -2 -2 -1 -2 -1 -2 -1 -2 -1 -2 -1 2 2 -1 -2 -2 -1 -2 -1 -2 -2 -1 2 -1 -2 -1 -2 -1 -2 -2 -1 \
   2 2 -1 -2 -2 -1 2 2 -1"

@[expose] def hsE9WH34 : List ℤ := parseInts hsE9WH34Str

@[expose] def hsWordP (w : List ℤ) : PArr := pWord 3850 [hsA0P, hsA1P] w

@[expose] def hsE9Check : Bool :=
  e9PackCheck 3850 (hsWordP hsE9WX) (hsWordP hsE9WY) (hsWordP hsE9WM1) (hsWordP hsE9WM2)
      (hsWordP hsE9WM3) (hsWordP hsE9WK) &&
    conjInvCheck 3850 (hsTP 5) (hsWordP hsE9WH5) (hsWordP hsE9WX) &&
    conjInvCheck 3850 (hsTP 12) (hsWordP hsE9WH12) (hsWordP hsE9WX) &&
    conjInvCheck 3850 (hsTP 21) (hsWordP hsE9WH21) (hsWordP hsE9WX) &&
    conjInvCheck 3850 (hsTP 34) (hsWordP hsE9WH34) (hsWordP hsE9WX)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
