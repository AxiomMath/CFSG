module

public import Certificates.Data.CoreD2Lines

public section

namespace Certificates.K36Spor

open CFSG.PSL3Four.Native Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

structure Cent where
  idx : Nat
  f1 : Nat
  f2 : Nat
deriving Inhabited

structure Exc where
  idx : Nat
  cW : List (List Int)
  cc : List Cent
  yW : List Int
  fWc : List (List Int)
  fyWc : List (List Int)
  wA : List Int
  wB : List Int
deriving Inhabited

structure SData where
  base : Data
  ys : List Nat
  gc : List Cent
  gen : List Nat
  wAs : List (List Int)
  wBs : List (List Int)
  exc : List Exc
  kCap : Nat
deriving Inhabited

@[expose] def yT (S : SData) (c : Cent) : Tab :=
  comp S.base.n (powT S.base.n (eT S.base 0) c.f1) (powT S.base.n (eT S.base (S.ys.getD c.idx 0)) c.f2)

@[expose] def centOK (S : SData) (c : Cent) (g : Tab) : Bool :=
  decide (c.idx < S.ys.length) && !(yT S c == idTab S.base.n) &&
    comp S.base.n g (yT S c) == comp S.base.n (yT S c) g

@[expose] def allowedS (S : SData) (i j : Nat) : Bool :=
  let c := S.gc.getD j default
  c.idx == i || c.f2 == 0

@[expose] def planesOK (S : SData) : Bool :=
  let D := S.base
  (D.eK == 2 || (D.eK == 3 && anyBelow D.eW.length fun i => anyBelow D.eW.length fun j =>
      !(comp D.n (eT D i) (eT D j) == comp D.n (eT D j) (eT D i)))) &&
    enumOK D.n (eGens D) (eEnum D) && (eEnum D).tabs.size == D.p ^ D.eK &&
    zOK D && S.ys.all (vOK D) && coverYOK ⟨D, S.ys, [], [], []⟩

@[expose] def invOK (S : SData) : Bool :=
  let D := S.base
  (allBelow 2 fun j => (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! (gsT D)[j]! == idTab D.n) &&
    (allBelow (gT D).size fun j =>
      (gTi D)[j]!.size == D.n && comp D.n (gTi D)[j]! (gT D)[j]! == idTab D.n)

@[expose] def genOK (S : SData) : Bool :=
  let D := S.base
  S.gc.length == D.gWs.length &&
    (allBelow (gT D).size fun j => centOK S (S.gc.getD j default) (gT D)[j]!) &&
    S.wAs.length == S.gen.length && S.wBs.length == S.gen.length &&
    allBelow S.gen.length fun k =>
      wordT D.n (gT D) (gTi D) (S.wAs.getD k []) == D.aT &&
        wordT D.n (gT D) (gTi D) (S.wBs.getD k []) == D.bT &&
        (S.wAs.getD k []).all (fun l => allowedS S (S.gen.getD k 0) (l.natAbs - 1)) &&
        (S.wBs.getD k []).all (fun l => allowedS S (S.gen.getD k 0) (l.natAbs - 1))

@[expose] def coverOKS (S : SData) : Bool :=
  allBelow S.ys.length fun i => S.gen.contains i || S.exc.any fun X => X.idx == i

@[expose] def planeTabs (S : SData) (i : Nat) : List Tab :=
  (List.range S.base.p).flatMap fun a => (List.range S.base.p).map fun b =>
    comp S.base.n (powT S.base.n (eT S.base 0) a) (powT S.base.n (eT S.base (S.ys.getD i 0)) b)

@[expose] def cT (S : SData) (X : Exc) : Array Tab := (X.cW.map (wT S.base)).toArray

@[expose] def cTi (S : SData) (X : Exc) : Array Tab := (cT S X).map (invTab S.base.n)

@[expose] def excOK (S : SData) (T : Array Tab) (X : Exc) : Bool :=
  let D := S.base
  let n := D.n
  let Y := planeTabs S X.idx
  let u := eT D 0
  let v := eT D (S.ys.getD X.idx 0)
  let cs := cT S X
  let ci := cTi S X
  let y := wT D X.yW
  let yi := invTab n y
  let f0 := wordT n cs ci (X.fWc.getD 0 [])
  let f1 := wordT n cs ci (X.fWc.getD 1 [])
  decide (X.idx < S.ys.length) &&
    (allBelow cs.size fun l => ci[l]!.size == n && comp n ci[l]! cs[l]! == idTab n) &&
    X.cc.length == X.cW.length &&
    (allBelow cs.size fun l =>
      (X.cc.getD l default).idx == X.idx && centOK S (X.cc.getD l default) cs[l]!) &&
    yi.size == n && comp n yi y == idTab n &&
    comp n y f0 == comp n (wordT n cs ci (X.fyWc.getD 0 [])) y &&
    comp n y f1 == comp n (wordT n cs ci (X.fyWc.getD 1 [])) y &&
    T.all (fun t => !(Y.any fun w => !(w == idTab n) && comp n t w == comp n w t) ||
      ((Y.any fun w => comp n t u == comp n w t) && (Y.any fun w => comp n t v == comp n w t))) &&
    T.all (fun t => !(comp n t u == comp n u t && comp n t v == comp n v t) || Y.any fun w => t == w) &&
    T.all (fun t => !(comp n t f0 == comp n f0 t && comp n t f1 == comp n f1 t) || t == idTab n) &&
    wordT n (cs.push y) (ci.push yi) X.wA == D.aT && wordT n (cs.push y) (ci.push yi) X.wB == D.bT

@[expose] def kEnum (S : SData) : Enum := enumBFS S.base.n (gsT S.base) S.kCap

@[expose] def checkS (S : SData) : Bool :=
  planesOK S && invOK S && genOK S && coverOKS S &&
    (S.exc.isEmpty ||
      (let E := kEnum S
       enumOK S.base.n (gsT S.base) E && S.exc.all (excOK S E.tabs)))

end Certificates.K36Spor
