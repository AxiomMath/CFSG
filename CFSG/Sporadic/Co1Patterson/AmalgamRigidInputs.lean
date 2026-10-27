module

public import CFSG.Sporadic.Co1Patterson.AmalgamInputs
public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Patterson.TwistNative
  CFSG.EvenSmallLie.OmegaEight

@[expose] def qRows : Rows := wRows (triW.getD 2 0)

@[expose] def pRows : Rows := wRows (triW.getD 0 0)

@[expose] def y0Idx : Nat := gensKe.getD 2 0

@[expose] def uBasis : List Nat := [2, 5, 9, 32, 64, 144]

@[expose] def eCols : List Nat := [8, 2, 13, 1, 192, 32, 64, 80]

@[expose] def qaeOK : Bool :=
  (List.range 256).all fun c =>
    [yprodRow c, mul (yprodRow c) iotaARows].all fun Y =>
      !qPts.contains (mul (mul (repXi 1) Y) (repX 1)) || Y == one || Y == qRows || Y == pRows ||
        Y == mul qRows pRows

@[expose] def edgeElemOK : Bool :=
  let K0 := gEl (gensKe.getD 4 0)
  let K0i := gElInv (gensKe.getD 4 0)
  let Y0 := gEl y0Idx
  let Y0i := gElInv y0Idx
  decide (1 ≤ y0Idx) && decide (y0Idx ≤ 190) &&
    mul (mul K0 pRows) K0i == mul qRows pRows &&
    mul (mul Y0 qRows) Y0i == qRows && mul (mul Y0 pRows) Y0i == mul qRows pRows &&
    qRows == mul (yprodRow 217) iotaARows && pRows == yprodRow 9 &&
    conjOK (repRows 1) eCols &&
    uBasis.all (fun c => colsApply eCols c == c) &&
    uBasis.all (fun c => mul (yprodRow c) (repRows 1) == mul (repRows 1) (yprodRow c)) &&
    colsApply eCols 1 == 8 && colsApply eCols 16 == 192

@[expose] def stabCond (y₁ y₂ : Nat) : Bool :=
  uBasis.all (fun c => bNat y₁ c == bNat 1 c && bNat y₂ c == bNat 16 c) &&
    CFSG.EvenSmallLie.OmegaEight.qNat y₁ == CFSG.EvenSmallLie.OmegaEight.qNat 1 &&
    CFSG.EvenSmallLie.OmegaEight.qNat y₂ == CFSG.EvenSmallLie.OmegaEight.qNat 16 &&
    bNat y₁ y₂ == bNat 1 16

@[expose] def stabOK : Bool :=
  (List.range 256).all fun y₁ => (List.range 256).all fun y₂ =>
    !stabCond y₁ y₂ || (y₁ == 1 && y₂ == 16) || (y₁ == 8 && y₂ == 192)

@[expose] def perpOK : Bool :=
  (List.range 256).all fun v =>
    !(uBasis.all fun c => !bNat v c) || v == 0 || v == 9 || v == 208 || v == 217

end CFSG.Sporadic.Co1Patterson.Native
