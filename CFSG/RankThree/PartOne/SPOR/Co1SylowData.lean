module

public import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
public import Certificates.Data.CFSGNative.Co1.TwoB
public meta import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
public meta import CFSG.RankThree.PartOne.SPOR.Co1PlanesDerivs
public meta import Certificates.Data.CFSGNative.Co1.TwoB

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative

@[expose] def co1SylowConj : List Int :=
    [32, 16, 12, 32, 16, -32, -28, 12, 16, -2, 2, 36, -8, 2, -2, -28, 8, 8, 28, -24, 1, -32, 32,
    -8, -32, 12, -12, 1, 24, -12, 20, 2, -8, -1, -8, 24, -32, -12, -1, 3, 1, 12, 32, -24, 8, 1,
    8, -2, -20, 12, -24, -1, 12, -12, 32, 8, -32, 32, -1, 24, -28, -8, -8, 28, 2, -2, 8, -36,
    -2, 2, -16, -12, 28, 32, -16, -32, -12, -16, -32]

@[expose] def co1SylowDerivs : List (List Int) :=
  co1PlaneADerivs0 ++ co1PlaneADerivs1.take 3 ++ [co1SylowConj, [3, 40], [38, 39, 39]]

@[expose] def co1SylowCentreOK (g₁ g₂ x p : Rows) : Bool :=
  !(mul p g₁ == mul g₁ p && mul p g₂ == mul g₂ p) || (List.range 5).any fun k => p == pow x k

@[noinline, expose] def co1SylowCheck (R : List Rows) (flag : Bool) (i₁ i₂ j : Nat) (T : GTree) :
    Bool :=
  flag && decide (1 ≤ i₁) && decide (i₁ ≤ R.length) && decide (1 ≤ i₂) && decide (i₂ ≤ R.length) &&
    decide (1 ≤ j) && decide (j ≤ R.length) && validRows (R.getD (i₁ - 1) one) &&
    validRows (R.getD (i₂ - 1) one) && validRows (R.getD (j - 1) one) &&
    gtOK #[R.getD (i₁ - 1) one, R.getD (i₂ - 1) one] T && decide (T.pts.size = 625) &&
    CFSG.Sporadic.Th.Native.allIn 0 T.pts.size (fun i =>
      co1SylowCentreOK (R.getD (i₁ - 1) one) (R.getD (i₂ - 1) one) (R.getD (j - 1) one)
        T.pts[i]!) &&
    pow (R.getD (j - 1) one) 5 == one

@[noinline, expose] def co1SylowOK (derivs : List (List Int)) (i₁ i₂ j : Nat) : Bool :=
  let D := dag co1PlaneBase derivs
  co1SylowCheck D.1 D.2.2 i₁ i₂ j (gtBFS #[D.1.getD (i₁ - 1) one, D.1.getD (i₂ - 1) one] 700)

end CFSG.RankThree.PartOne.SPOR
