module

public import CFSG.RankThree.PartOne.SPOR.Co1PlanesDerivs
public import CFSG.Sporadic.Co1Block.Iota
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import Certificates.Data.CFSGNative.Co1.Involutions
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1Block

structure Co1PlaneBlock1 where
  p : Nat
  y : Nat
  wit : List Nat
  ex : Nat

structure Co1PlaneBlock2 where
  p : Nat
  y1 : Nat
  y2 : Nat
  wits : List (List Nat)
  exps : List Nat

structure Co1PlaneClass where
  derivs : List (List Int)
  t : Nat
  b1 : List Co1PlaneBlock1
  b2 : List Co1PlaneBlock2

@[expose] def co1PlaneBase : List Rows := [aR, bR, iotaARows, iotaCRows]

@[expose] def co1ConjProd (R : List Rows) (tR : Rows) (ws : List Nat) : Rows :=
  ws.foldr (fun k acc =>
    mul (mul (mul (R.getD (k - 1) one) tR) (inv (R.getD (k - 1) one))) acc) one

@[noinline, expose] def co1LineOK (R : List Rows) (tR : Rows) (p : Nat) (x : Rows) (ws : List Nat)
    (ex : Nat) : Bool :=
  ws.all (fun k => decide (1 ≤ k) && decide (k ≤ R.length) &&
      mul (R.getD (k - 1) one) (inv (R.getD (k - 1) one)) == one &&
      mul (R.getD (k - 1) one) x == mul x (R.getD (k - 1) one)) &&
    validRows (pow (co1ConjProd R tR ws) ex) && pow (co1ConjProd R tR ws) ex != one &&
    pow (pow (co1ConjProd R tR ws) ex) p == one

@[noinline, expose] def co1Block1OK (R : List Rows) (tR : Rows) (b : Co1PlaneBlock1) : Bool :=
  decide (1 ≤ b.y) && decide (b.y ≤ R.length) && validRows (R.getD (b.y - 1) one) &&
    mul (R.getD (b.y - 1) one) tR == mul tR (R.getD (b.y - 1) one) &&
    pow (R.getD (b.y - 1) one) b.p == one && R.getD (b.y - 1) one != one &&
    co1LineOK R tR b.p (R.getD (b.y - 1) one) b.wit b.ex

@[noinline, expose] def co1Block2OK (R : List Rows) (tR : Rows) (b : Co1PlaneBlock2) : Bool :=
  decide (1 ≤ b.y1) && decide (b.y1 ≤ R.length) && decide (1 ≤ b.y2) && decide (b.y2 ≤ R.length) &&
    validRows (R.getD (b.y1 - 1) one) && validRows (R.getD (b.y2 - 1) one) &&
    mul (R.getD (b.y1 - 1) one) tR == mul tR (R.getD (b.y1 - 1) one) &&
    mul (R.getD (b.y2 - 1) one) tR == mul tR (R.getD (b.y2 - 1) one) &&
    pow (R.getD (b.y1 - 1) one) b.p == one && pow (R.getD (b.y2 - 1) one) b.p == one &&
    mul (R.getD (b.y1 - 1) one) (R.getD (b.y2 - 1) one) ==
      mul (R.getD (b.y2 - 1) one) (R.getD (b.y1 - 1) one) &&
    (List.range b.p).all (fun a => (List.range b.p).all fun c => (List.range b.p).all fun a' =>
      (List.range b.p).all fun c' => (decide (a = a') && decide (c = c')) ||
        (validRows (mul (pow (R.getD (b.y1 - 1) one) a) (pow (R.getD (b.y2 - 1) one) c)) &&
          validRows (mul (pow (R.getD (b.y1 - 1) one) a') (pow (R.getD (b.y2 - 1) one) c')) &&
          mul (pow (R.getD (b.y1 - 1) one) a) (pow (R.getD (b.y2 - 1) one) c) !=
            mul (pow (R.getD (b.y1 - 1) one) a') (pow (R.getD (b.y2 - 1) one) c'))) &&
    b.wits.length == b.p + 1 && b.exps.length == b.p + 1 &&
    co1LineOK R tR b.p (R.getD (b.y2 - 1) one) (b.wits.getD 0 []) (b.exps.getD 0 0) &&
    (List.range b.p).all fun c => co1LineOK R tR b.p
      (mul (R.getD (b.y1 - 1) one) (pow (R.getD (b.y2 - 1) one) c)) (b.wits.getD (c + 1) [])
      (b.exps.getD (c + 1) 0)

@[noinline, expose] def co1ClassOK (c : Co1PlaneClass) : Bool :=
  (dag co1PlaneBase c.derivs).2.2 && decide (1 ≤ c.t) && decide (c.t ≤ co1PlaneBase.length) &&
    c.b1.all (co1Block1OK (dag co1PlaneBase c.derivs).1
      ((dag co1PlaneBase c.derivs).1.getD (c.t - 1) one)) &&
    c.b2.all (co1Block2OK (dag co1PlaneBase c.derivs).1
      ((dag co1PlaneBase c.derivs).1.getD (c.t - 1) one))

@[expose] def co1PlaneA : Co1PlaneClass where
  derivs := co1PlaneADerivs
  t := 3
  b1 := [{ p := 7, y := 47, wit := [3, 48, 49], ex := 1 }]
  b2 := [{ p := 5, y1 := 38, y2 := 39,
            wits := [[3, 40], [3, 41], [3, 42], [3, 43], [3, 44], [3, 45]],
            exps := [1, 1, 1, 1, 1, 1] }]

@[expose] def co1PlaneC : Co1PlaneClass where
  derivs := co1PlaneCDerivs
  t := 4
  b1 := [{ p := 5, y := 38, wit := [4, 39], ex := 1 }]
  b2 := []

@[expose] def co1PlaneB : Co1PlaneClass where
  derivs := co1PlaneBDerivs
  t := 1
  b1 := [{ p := 7, y := 53, wit := [1, 56, 57], ex := 1 }]
  b2 := [{ p := 5, y1 := 46, y2 := 47,
            wits := [[1, 48], [1, 49], [1, 50], [1, 54], [1, 55], [1, 51]],
            exps := [1, 1, 1, 1, 1, 1] }]

end CFSG.RankThree.PartOne.SPOR
