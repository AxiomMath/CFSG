module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheckInputs
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.Sporadic.Schreier.RuCore
public import Certificates.Data.W4RowConjInv
public import CFSG.Sporadic.HeldB.InnerCheck

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab

@[expose] def e25PackCheck (n : ℕ) (x y m₁ m₂ m₃ m₄ m₅ : PArr) : Bool :=
  let e := idA n
  eqA n (powA n x.1 5) e && eqA n (powA n y.1 5) e && !eqA n x.1 e &&
    eqA n (compA n x.1 y.1) (compA n y.1 x.1) && allLt 5 (fun j => !eqA n y.1 (powA n x.1 j)) &&
    eqA n (compA n (compA n m₁.1 x.1) m₁.2) y.1 &&
    eqA n (compA n (compA n m₂.1 x.1) m₂.2) (compA n x.1 y.1) &&
    eqA n (compA n (compA n m₃.1 x.1) m₃.2) (compA n x.1 (powA n y.1 2)) &&
    eqA n (compA n (compA n m₄.1 x.1) m₄.2) (compA n x.1 (powA n y.1 3)) &&
    eqA n (compA n (compA n m₅.1 x.1) m₅.2) (compA n x.1 (powA n y.1 4))

@[expose] def heE25WXStr : String :=
  "-1 -2 -1 -2 -2 -2 -2 -1 2 2 2 1 -2 -2 1 -2 1 -2 -2 -1 -2 -2 -2 -2 -2 -2 -1 -2 -2 -2 -1 2 2 2 \
   2 1 2 2 2 1 2 2 1 -2 1 -2 -1 2 -1 2 -1 2 -1 2 -1 -2 -1 -2 -2 -2 -1 -2 -1 -2 1 2 1 -2 -2 -2 \
   -1"

@[expose] def heE25WX : List ℤ := parseInts heE25WXStr

@[expose] def heE25WYStr : String :=
  "-2 -1 -2 -1 2 -1 2 -1 -2 -2 -1 -2 -2 -2 -2 -1 -2 -2 -2 -1 2 2 -1 -2 -2 -2 -2 -2 -2 -1 -2 -2 \
   -2 -1 2 2 -1 -2 -2 -1 2 2 2 1 -2 -2 -2 1 2 2 1 2 1 -2 -2 -2 1 2 2 2 2 1 -2 1 2 2 -1 -2 -1 2 \
   -1 -2 -2 -1 2 -1 -2 -2 -1"

@[expose] def heE25WY : List ℤ := parseInts heE25WYStr

@[expose] def heE25WM1Str : String :=
  "-2 -1 -2 -2 -2 -1 -2 -2 -1 -2 -1 2 2 2 -1 -2 -2 -1 -2 -2 -2 -2 -2 -2 -2 -2 -1 -2 -2 -2 -1 2 \
   2 -1 -2 -2 -1 2 2 -1 -2 -2 -2 -2 -2 -2 -1 -2 -1 2 -1 -2 -1 -2 -2 -1 2 2 -1 2 -1 -2 -2 -2 -1 \
   2 2 2 -1 -2 -2 -2 -2 1 -2 1 2 1 2 2 1 2 1 2 1 2 1 2 -1"

@[expose] def heE25WM1 : List ℤ := parseInts heE25WM1Str

@[expose] def heE25WM2Str : String :=
  "-1 -2 -2 -1 -2 -1 -2 -2 -1 -2 -2 -2 -1 -2 -1 -2 -2 -1 2 2 -1 -2 -2 -1 -2 -2 -2 -2 -1 -2 -1 \
   -2 -2 -1 2 2 2 1 -2 1 -2 -2 1 2 2 2 1 -2 1 -2 -2 1 2 2 2 1 2 1 2 1 2 -1 2 -1 2 -1 2 -1 2 2 \
   -1 -2 -2 -1"

@[expose] def heE25WM2 : List ℤ := parseInts heE25WM2Str

@[expose] def heE25WM3Str : String :=
  "-2 -2 1 2 2 1 -2 -2 1 2 2 2 1 -2 1 -2 -2 1 2 2 2 1 2 2 2 2 1 2 2 1 2 1 2 2 2 2 2 2 1 2 1 2 2 \
   2 2 2 2 1 -2 -2 1 2 2 1 -2 -2 1 2 2 2 1 2 2 2 2 2 2 2 2 1 2 1 2 2 1 2 1 2 2 1 2 2 1"

@[expose] def heE25WM3 : List ℤ := parseInts heE25WM3Str

@[expose] def heE25WM4Str : String :=
  "-2 -1 -2 -2 -2 -1 -2 -2 -1 2 -1 2 -1 -2 -2 -1 -2 -2 -2 -2 -1 -2 -2 -2 -2 -1 -2 -2 -2 -1 2 2 \
   -1 -2 -2 -1 -2 -2 -2 -2 -1 -2 -1 -2 -2 -2 -2 -2 -2 -1 -2 -1 2 -1 -2 -2 -2 -1 2 2 2 -1 -2 -1 \
   -2 -2 -1 2 2 2 2 1 -2 -2 1 -2 1 -2 1 -2 1 -2 -1 -2 -1 -2 -2"

@[expose] def heE25WM4 : List ℤ := parseInts heE25WM4Str

@[expose] def heE25WM5Str : String :=
  "-1 -2 -1 -2 -1 -2 -2 -1 -2 -1 2 2 -1 -2 -2 -2 -1 -2 -2 -1 -2 -2 -2 -2 -1 -2 -1 -2 -2 -2 -2 \
   -2 -2 -1 -2 -2 -1 -2 -1 -2 -1 2 -1 2 -1 2 2 -1 -2 -2 -2 -1 2 2 2 2 1 -2 -2 1 -2 1 -2 1 -2 1 \
   -2 -1 -2 -1 -2 -1 -2"

@[expose] def heE25WM5 : List ℤ := parseInts heE25WM5Str

@[expose] def heE25WH0Str : String :=
  "-2 -2 1 2 2 2 1 -2 1 -2 -2 1 2 2 1 -2 -2 1 2 2 2 1 2 2 2 2 2 2 1 -2 -2 1 -2 1 2 1 2 1 2 2 1 \
   2 2 2 2 1 2 1"

@[expose] def heE25WH0 : List ℤ := parseInts heE25WH0Str

@[expose] def heE25WH1Str : String :=
  "2 2 1 -2 1 2 2 1 -2 1 -2 1 2 -1 -2 -2 -2 -2 1 2 2 1 2 1 -2 1 2 1 -2 1 -2 -2 1 2 2 1 -2 -2 1 \
   2 2 2 1 2 2 2 2 2 2 1 -2 1 2 2 2 1 2 1 2 1 2 2"

@[expose] def heE25WH1 : List ℤ := parseInts heE25WH1Str

@[expose] def heE25WHUStr : String :=
  "1 2 1 2 1 -2 1 2 1 -2 1 2 1 -2 -2 -2 -1 -2 -1 2 2 2 -1 -2 -1 -2 -2 -1 -2 -2 -1 2 -1 2 1 2 1 \
   2 2 2 1 2 2 1 2 2 1 2 1 2 2 1 2 2"

@[expose] def heE25WHU : List ℤ := parseInts heE25WHUStr

@[expose] def heWordP (w : List ℤ) : PArr := pWord 8330 [heA0P, heA1P] w

@[expose] def heE25Check : Bool :=
  e25PackCheck 8330 (heWordP heE25WX) (heWordP heE25WY) (heWordP heE25WM1) (heWordP heE25WM2)
      (heWordP heE25WM3) (heWordP heE25WM4) (heWordP heE25WM5) &&
    conjInvCheck 8330 heT0P (heWordP heE25WH0) (heWordP heE25WX) &&
    conjInvCheck 8330 heT1ArrP (heWordP heE25WH1) (heWordP heE25WX) &&
    conjInvCheck 8330 heUP (heWordP heE25WHU) (heWordP heE25WX)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
