module

public import Certificates.Data.CoreD2Perm

public section

namespace Certificates.CoreD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

structure GKind where
  kind : Nat
  idx : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
deriving Inhabited

structure VData where
  base : Data
  ys : List Nat
  gk : List GKind
  wAs : List (List Int)
  wBs : List (List Int)
deriving Inhabited

@[expose] def zOK (D : Data) : Bool :=
  decide (0 < D.eW.length) && powT D.n (eT D 0) D.p == idTab D.n && !(eT D 0 == idTab D.n) &&
    allBelow D.eW.length fun k => comp D.n (eT D 0) (eT D k) == comp D.n (eT D k) (eT D 0)

@[expose] def vOK (D : Data) (j : Nat) : Bool :=
  decide (j < D.eW.length) && powT D.n (eT D j) D.p == idTab D.n &&
    allBelow D.p fun k => !(eT D j == powT D.n (eT D 0) k)

@[expose] def kindOK (V : VData) (j : Nat) : Bool :=
  let D := V.base
  let f := V.gk.getD j default
  let u := eT D 0
  let v := eT D (V.ys.getD f.idx 0)
  let g := (gT D)[j]!
  decide (f.idx < V.ys.length) &&
    (if f.kind == 0 then
      comp D.n g u == comp D.n (comp D.n (powT D.n u f.f1) (powT D.n v f.f2)) g &&
        comp D.n g v == comp D.n (comp D.n (powT D.n u f.f3) (powT D.n v f.f4)) g
    else
      !(comp D.n (powT D.n u f.f1) (powT D.n v f.f2) == idTab D.n) &&
        powT D.n (comp D.n (powT D.n u f.f1) (powT D.n v f.f2)) D.p == idTab D.n &&
        comp D.n g (comp D.n (powT D.n u f.f1) (powT D.n v f.f2)) ==
          comp D.n (powT D.n (comp D.n (powT D.n u f.f1) (powT D.n v f.f2)) f.f3) g)

@[expose] def allowed (V : VData) (i j : Nat) : Bool :=
  let f := V.gk.getD j default
  f.kind == 0 || f.idx == i || f.f2 == 0

@[expose] def wordOK (V : VData) (i : Nat) (w : List Int) : Bool :=
  w.all fun l => allowed V i (l.natAbs - 1)

@[expose] def coverYOK (V : VData) : Bool :=
  (eEnum V.base).tabs.all fun t =>
    anyBelow V.ys.length fun i => anyBelow V.base.p fun a => anyBelow V.base.p fun b =>
      t == comp V.base.n (powT V.base.n (eT V.base 0) a)
        (powT V.base.n (eT V.base (V.ys.getD i 0)) b)

@[expose] def checkV (V : VData) : Bool :=
  V.base.eK == 3 &&
    (anyBelow V.base.eW.length fun i => anyBelow V.base.eW.length fun j =>
      !(comp V.base.n (eT V.base i) (eT V.base j) == comp V.base.n (eT V.base j) (eT V.base i))) &&
    (allBelow 2 fun j => (giT V.base)[j]!.size == V.base.n &&
      comp V.base.n (giT V.base)[j]! (gsT V.base)[j]! == idTab V.base.n) &&
    (allBelow (gT V.base).size fun j => (gTi V.base)[j]!.size == V.base.n &&
      comp V.base.n (gTi V.base)[j]! (gT V.base)[j]! == idTab V.base.n) &&
    enumOK V.base.n (eGens V.base) (eEnum V.base) &&
    (eEnum V.base).tabs.size == V.base.p ^ V.base.eK &&
    zOK V.base && V.ys.all (vOK V.base) && coverYOK V &&
    V.gk.length == V.base.gWs.length && allBelow (gT V.base).size (kindOK V) &&
    V.wAs.length == V.ys.length && V.wBs.length == V.ys.length &&
    allBelow V.ys.length fun i =>
      wordT V.base.n (gT V.base) (gTi V.base) (V.wAs.getD i []) == V.base.aT &&
        wordT V.base.n (gT V.base) (gTi V.base) (V.wBs.getD i []) == V.base.bT &&
        wordOK V i (V.wAs.getD i []) && wordOK V i (V.wBs.getD i [])

end Certificates.CoreD2Perm
