module

public import CFSG.Quasithin.H13.J4Normal3
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Mathieu.M22
public meta import Certificates.Data.CFSGNative.H13.J4Local
public meta import CFSG.Quasithin.H13.J4QuotGroup
import Certificates.Data.CFSGNative.H13.J4Local

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Quasithin.H13.J4.Native TauCeti

@[expose] def alphaW : List (ℕ × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)]

@[expose] def betaW : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, false), (0, true)]

@[expose] def m22Rels : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, false),
      (1, true)],
    [(0, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true),
      (0, false), (1, false)],
    [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true),
      (1, true), (1, true), (1, true)]]

@[expose] def genW : List (List (ℕ × Bool)) :=
  [[(0, true), (1, true), (1, true), (0, true), (0, true), (1, false), (1, false), (0, false),
      (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, false)],
    [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, true)]]

@[expose] def aPair : Pr12 := pr12BWord #[xPair, yPair] alphaW

@[expose] def bPair : Pr12 := pr12BWord #[xPair, yPair] betaW

@[expose] def m22Checks : Bool :=
  m22Rels.all (fun r => eqModZ zPair (pr12BWord #[aPair, bPair] r).1
      (CFSG.Sporadic.SmallF2.Native.idRows 12)) &&
    eqModZ zPair (pr12BWord #[aPair, bPair] (genW.getD 0 [])).1 xPair.1 &&
    eqModZ zPair (pr12BWord #[aPair, bPair] (genW.getD 1 [])).1 yPair.1

end CFSG.Quasithin.H13.J4
