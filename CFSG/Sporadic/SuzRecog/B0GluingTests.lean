module

public import CFSG.Sporadic.SuzRecog.C1ModelTests
public import Certificates.Data.B0GluingData

public section

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzRecog.B0GluingData

@[expose] def fpIndex (T : Array Tab) : Array Nat := Id.run do
  let mut m : Array Nat := Array.replicate 1782 T.size
  for k in [0:T.size] do
    m := m.set! (T[k]!)[0]! k
  return m

@[expose] def ttabs : Array Tab := t0Enum.tabs

@[expose] def tFp : Array Nat := fpIndex ttabs

@[expose] def tPos (x : Tab) : Nat := tFp[x[0]!]!

@[expose] def tFound (x : Tab) : Bool := decide (tPos x < 64) && ttabs[tPos x]! == x

@[expose] def mulI : Array (Array Nat) :=
  Array.ofFn (n := 64) fun a => Array.ofFn (n := 64) fun b =>
    tFp[(ttabs[a.val]!)[(ttabs[b.val]!)[0]!]!]!

@[expose] def mulP (a b : Nat) : Nat := (mulI[a]!)[b]!

@[expose] def oneI : Nat := tPos (idTab 1782)

@[expose] def invI : Array Nat :=
  Array.ofFn (n := 64) fun a => ((List.range 64).find? fun b => mulP a.val b == oneI).getD 0

@[expose] def invP (a : Nat) : Nat := invI[a]!

@[expose] def cmI : Array (Array Nat) :=
  Array.ofFn (n := 64) fun a => Array.ofFn (n := 64) fun b =>
    mulP (mulP a.val b.val) (mulP (invP a.val) (invP b.val))

@[expose] def cmP (a b : Nat) : Nat := (cmI[a]!)[b]!

@[expose] def gP (i : Nat) : Nat := tPos t0Tabs[i]!

@[expose] def zI : Array Nat :=
  #[oneI, tPos tTab, cmP (gP 0) (gP 3), mulP (cmP (gP 0) (gP 3)) (tPos tTab)]

@[expose] def cosP (a : Nat) : Nat :=
  min (min (mulP a zI[0]!) (mulP a zI[1]!)) (min (mulP a zI[2]!) (mulP a zI[3]!))

@[expose] def gammaGen (r i : Nat) : Nat := mulP (gP i) zI[(gammaReps.getD r []).getD i 0]!

@[expose] def gammaI (r : Nat) : Array Nat := Id.run do
  let mut m : Array Nat := Array.replicate 64 oneI
  for k in [1:64] do
    m := m.set! k (mulP (gammaGen r t0Enum.lab[k]!) m[t0Enum.par[k]!]!)
  return m

@[expose] def gammaIs : Array (Array Nat) := Array.ofFn (n := 16) fun r => gammaI r.val

@[expose] def invPerm (g : Array Nat) : Array Nat :=
  Array.ofFn (n := 64) fun k => ((List.range 64).find? fun x => g[x]! == k.val).getD 0

@[expose] def gammaInvIs : Array (Array Nat) := gammaIs.map invPerm

@[expose] def chiBit (v i : Nat) : Nat := ((v + 1) / 2 ^ i) % 2

@[expose] def chiI (v : Nat) : Array Nat := Id.run do
  let mut m : Array Nat := Array.replicate 64 0
  for k in [1:64] do
    m := m.set! k ((chiBit v t0Enum.lab[k]! + m[t0Enum.par[k]!]!) % 2)
  return m

@[expose] def chiIs : Array (Array Nat) := Array.ofFn (n := 15) fun v => chiI v.val

@[expose] def idxCheck : Bool :=
  (allBelow 64 fun a => allBelow 64 fun b =>
    decide (mulP a b < 64) && ttabs[mulP a b]! == comp 1782 ttabs[a]! ttabs[b]!) &&
    tFound (idTab 1782) && oneI == 0 && (allBelow 4 fun i => tFound t0Tabs[i]!) && tFound tTab &&
    (allBelow 64 fun a => decide (invP a < 64) && mulP a (invP a) == oneI) &&
    (allBelow 4 fun i => mulP (gP i) (gP i) == oneI) &&
    cmP (gP 0) (gP 1) == oneI && cmP (gP 2) (gP 3) == oneI &&
    cmP (gP 0) (gP 2) == cmP (gP 1) (gP 3) &&
    mulP (mulP (cmP (gP 0) (gP 3)) (cmP (gP 1) (gP 2))) (cmP (gP 0) (gP 2)) == oneI &&
    (allBelow 64 fun a => mulP zI[2]! a == mulP a zI[2]!) && mulP zI[2]! zI[2]! == oneI &&
    (allBelow 15 fun v =>
      let ch := chiIs[v]!
      ch[0]! == 0 &&
      (allBelow 64 fun k =>
        k == 0 || ch[k]! == (chiBit v t0Enum.lab[k]! + ch[t0Enum.par[k]!]!) % 2) &&
      (allBelow 64 fun a => allBelow 64 fun b => ch[mulP a b]! == (ch[a]! + ch[b]!) % 2) &&
      anyBelow 4 fun i => ch[gP i]! == 1) &&
    allBelow 16 fun r =>
      let g := gammaIs[r]!
      let gi := gammaInvIs[r]!
      g[0]! == oneI &&
      (allBelow 64 fun k =>
        k == 0 || g[k]! == mulP (gammaGen r t0Enum.lab[k]!) g[t0Enum.par[k]!]!) &&
      allBelow 64 fun k => decide (gi[k]! < 64) && g[gi[k]!]! == k

@[expose] def rtabs : Array Tab := ttabs.map resTab

@[expose] def rIdx : Std.HashMap Tab Nat := indexOf rtabs

@[expose] def thetaTab (i : Nat) : Tab := wordTab 42 gTabs (thetaWords.getD i [])

@[expose] def thetaInvTab (i : Nat) : Tab := invTab 42 (thetaTab i)

@[expose] def thetaPerm (i : Nat) : Array Nat :=
  Array.ofFn (n := 64) fun k =>
    posOf rIdx rtabs (conjTab 42 (thetaTab i) (thetaInvTab i) rtabs[k.val]!)

@[expose] def thetaPerms : Array (Array Nat) := Array.ofFn (n := 36) fun i => thetaPerm i.val

@[expose] def thetaInvPerms : Array (Array Nat) := thetaPerms.map invPerm

@[expose] def thetaCheck : Bool :=
  allBelow 36 fun i =>
    let θ := thetaTab i
    let θi := thetaInvTab i
    let p := thetaPerms[i]!
    let q := thetaInvPerms[i]!
    θi.size == 42 && comp 42 θi θ == idTab 42 &&
      (allBelow 64 fun k => decide (p[k]! < 64) && rtabs[p[k]!]! == conjTab 42 θ θi rtabs[k]!) &&
      allBelow 64 fun k => decide (q[k]! < 64) && p[q[k]!]! == k

@[expose] def keyOf (a b c d : Nat) : List Nat := [cosP a, cosP b, cosP c, cosP d, cmP a c, cmP a d]

@[expose] def thetaKey (i : Nat) : List Nat :=
  let p := thetaPerms[i]!
  keyOf p[gP 0]! p[gP 1]! p[gP 2]! p[gP 3]!

@[expose] def ctGamma (t r i : Nat) : Nat := mulP (mulP t (gammaGen r i)) (invP t)

@[expose] def dictOf (q₀ q₁ q₂ q₃ : Nat) : Option (Nat × Nat) :=
  (List.range 64).findSome? fun t =>
    if cosP (ctGamma t 0 0) == cosP q₀ && cosP (ctGamma t 0 1) == cosP q₁ &&
        cosP (ctGamma t 0 2) == cosP q₂ && cosP (ctGamma t 0 3) == cosP q₃ then
      ((List.range 16).find? fun r => ctGamma t r 0 == q₀ && ctGamma t r 1 == q₁ &&
        ctGamma t r 2 == q₂ && ctGamma t r 3 == q₃).map fun r => (t, r)
    else none

@[expose] def decompOf (a b c d : Nat) : Option (Nat × Nat × Nat) :=
  ((List.range 36).find? (fun i => thetaKey i == keyOf a b c d)).bind fun i =>
    let q := thetaInvPerms[i]!
    (dictOf q[a]! q[b]! q[c]! q[d]!).map fun x => (i, x.1, x.2)

@[expose] def decompEq (i t r a b c d : Nat) : Bool :=
  let p := thetaPerms[i]!
  decide (i < 36) && decide (t < 64) && decide (r < 16) &&
    a == p[ctGamma t r 0]! && b == p[ctGamma t r 1]! && c == p[ctGamma t r 2]! &&
    d == p[ctGamma t r 3]!

@[expose] def decompOK (a b c d : Nat) : Bool :=
  (decompOf a b c d).any fun x => decompEq x.1 x.2.1 x.2.2 a b c d

@[expose] def inKer (a b c d : Nat) : Bool :=
  anyBelow 15 fun v => let ch := chiIs[v]!
    ch[a]! == 0 && ch[b]! == 0 && ch[c]! == 0 && ch[d]! == 0

@[expose] def invPs : List Nat := (List.range 64).filter fun a => mulP a a == oneI

@[expose] def cPairs : List (Nat × Nat) :=
  invPs.flatMap fun a => (invPs.filter fun b => cmP a b == oneI).map fun b => (a, b)

@[expose] def autCheck : Bool :=
  cPairs.all fun p => cPairs.all fun q =>
    !(cmP p.1 q.1 == cmP p.2 q.2 &&
        mulP (mulP (cmP p.1 q.2) (cmP p.2 q.1)) (cmP p.1 q.1) == oneI) ||
      inKer p.1 p.2 q.1 q.2 || decompOK p.1 p.2 q.1 q.2

@[expose] def radPos (X : Nat) : Array Nat :=
  ((List.range 64).filter fun k =>
    cmP k (gP (2 * X)) == oneI && cmP k (gP (2 * X + 1)) == oneI).toArray

@[expose] def rads : Array (Array Nat) := #[radPos 0, radPos 1]

@[expose] def radIdx (X : Nat) : Array Nat := Id.run do
  let E := rads[X]!
  let mut m : Array Nat := Array.replicate 64 16
  for i in [0:E.size] do
    m := m.set! E[i]! i
  return m

@[expose] def radIdxs : Array (Array Nat) := #[radIdx 0, radIdx 1]

@[expose] def inRad (X e : Nat) : Bool :=
  decide ((radIdxs[X]!)[e]! < 16) && (rads[X]!)[(radIdxs[X]!)[e]!]! == e

@[expose] def r0Tabs : Array Tab := #[idTab 1782, w0T, r1T, r2T]

@[expose] def y0TabsOf (X : Nat) : Array Tab :=
  Array.ofFn (n := 64) fun p => comp 1782 ttabs[(rads[X]!)[p.val / 4]!]! r0Tabs[p.val % 4]!

@[expose] def y0Tabs : Array (Array Tab) := #[y0TabsOf 0, y0TabsOf 1]

@[expose] def y0Fps : Array (Array Nat) := #[fpIndex y0Tabs[0]!, fpIndex y0Tabs[1]!]

@[expose] def y0Pos (X : Nat) (y : Tab) : Nat := (y0Fps[X]!)[y[0]!]!

@[expose] def jTab (w : List Nat) : Tab := wordTab 1782 #[tTab, C1Model.zT] w

@[expose] def nTabs : Array Tab :=
  #[jTab (witJ1.getD 0 []), jTab (witJ2.getD 0 []), jTab (witJ1.getD 1 []), jTab (witJ2.getD 1 [])]

@[expose] def nInvs : Array Tab := nTabs.map (invTab 1782)

@[expose] def nActs : Array (Array Nat) :=
  Array.ofFn (n := 4) fun l => Array.ofFn (n := 64) fun k =>
    let y := conjTab 1782 nTabs[l.val]! nInvs[l.val]! ttabs[k.val]!
    if tFound y then tPos y else 64

@[expose] def jE (l r e : Nat) : Nat :=
  let k := (nActs[l]!)[(gammaIs[r]!)[e]!]!
  if k < 64 then (gammaInvIs[r]!)[k]! else 64

@[expose] def jAct (X l r p : Nat) : Nat :=
  4 * (radIdxs[X]!)[jE l r (rads[X]!)[p / 4]!]! + p % 4

@[expose] def cTabW (X : Nat) : Tab := decTab (witC.getD X ([], 0))

@[expose] def cTabsW : Array Tab := #[cTabW 0, cTabW 1]

@[expose] def cInvsW : Array Tab := cTabsW.map (invTab 1782)

@[expose] def cActs : Array (Array Nat) :=
  Array.ofFn (n := 2) fun X => Array.ofFn (n := 64) fun p =>
    y0Pos X.val (conjTab 1782 cTabsW[X.val]! cInvsW[X.val]! (y0Tabs[X.val]!)[p.val]!)

@[expose] def hAct (r p : Nat) : Nat :=
  let X := witRadical.getD r 0
  jAct X (2 * X + 1) r ((cActs[X]!)[jAct X (2 * X) r p]!)

@[expose] def pT1 (X : Nat) : Nat := 4 * (radIdxs[X]!)[zI[1]!]!

@[expose] def pR0 (X ρ : Nat) : Nat := 4 * (radIdxs[X]!)[oneI]! + ρ

@[expose] def letterOK (X r : Nat) : Bool :=
  allBelow 2 fun s => allBelow 16 fun i =>
    let e' := jE (2 * X + s) r (rads[X]!)[i]!
    decide (e' < 64) && inRad X e'

@[expose] def radOK (X : Nat) : Bool :=
  let E := rads[X]!
  let c := cTabsW[X]!
  let ci := cInvsW[X]!
  let A := cActs[X]!
  let Y := y0Tabs[X]!
  E.size == 16 && (allBelow 16 fun i => decide (E[i]! < 64) && inRad X E[i]!) &&
    ci.size == 1782 && comp 1782 ci c == idTab 1782 &&
    (allBelow 64 fun p => decide (A[p]! < 64) && Y[A[p]!]! == conjTab 1782 c ci Y[p]!) &&
    inRad X oneI && inRad X zI[1]!

@[expose] def planeCheck : Bool :=
  (allBelow 1782 fun i => (w0T[i]! == i) == (r1T[i]! == i)) &&
    (allBelow 4 fun l => (nInvs[l]!).size == 1782 && comp 1782 nInvs[l]! nTabs[l]! == idTab 1782) &&
    radOK 0 && radOK 1 &&
    allBelow 15 fun r' =>
      let r := r' + 1
      let X := witRadical.getD r 0
      let a := (y0Tabs[X]!)[hAct r (pR0 X 1)]!
      let b := (y0Tabs[X]!)[hAct r (pR0 X 2)]!
      decide (X < 2) && letterOK X r && hAct r (pT1 X) == pT1 X &&
        anyBelow 1782 fun i => a[i]! == i && !(b[i]! == i)

@[expose] def p0Gens : Array Tab := Array.ofFn (n := 4) fun i => resTab t0Tabs[i.val]!

@[expose] def zRes : Array Tab := Array.ofFn (n := 4) fun j => rtabs[zI[j.val]!]!

@[expose] def eAdj (x y : Nat) : Bool := (eNbr.getD x []).contains y

@[expose] def eInv (g : Tab) : Bool :=
  allBelow 42 fun x => allBelow 42 fun y => eAdj x y == eAdj g[x]! g[y]!

@[expose] def wordAt (P : Nat → Nat → Nat) (w : List Nat) (y : Nat) : Nat :=
  w.foldr (fun k y => P k y) y

@[expose] def cMap (P : Nat → Nat → Nat) (b : List Nat) (x : Nat) : Nat :=
  wordAt P (cWords.getD x (0, [])).2 (b.getD (cWords.getD x (0, [])).1 0)

@[expose] def stabOK (P : Nat → Nat → Nat) (a b : Nat) : Bool :=
  allBelow 4 fun k => !(P k a == a) || P k b == b

@[expose] def cCands (b : List Nat) : List Nat :=
  if b.length = 0 then List.range 42 else eNbr.getD (b.getD (cPar.getD b.length 0) 0) []

@[expose] def eMap (f : Nat → Nat) : Bool :=
  allBelow 42 fun x => (eNbr.getD x []).all fun y => eAdj (f x) (f y)

@[expose] def onto42 (f : Nat → Nat) : Bool := allBelow 42 fun y => anyBelow 42 fun x => f x == y

@[expose] def cLeaf (P Z : Nat → Nat → Nat) (b : List Nat) : Bool :=
  (anyBelow 4 fun j => allBelow 42 fun x => cMap P b x == Z j x) ||
    !(onto42 (cMap P b) &&
      (allBelow 4 fun k => allBelow 42 fun y => cMap P b (P k y) == P k (cMap P b y)) &&
      eMap (cMap P b))

@[expose] def cSearch (P Z : Nat → Nat → Nat) : Nat → List Nat → Bool
  | 0, b => cLeaf P Z b
  | f + 1, b => (cCands b).all fun c =>
    !stabOK P (cReps.getD b.length 0) c || cSearch P Z f (b ++ [c])

@[expose] def cDataOK (P : Nat → Nat → Nat) : Bool :=
  cReps.length == 6 && cReps.all (· < 42) &&
    (allBelow 5 fun i => decide (cPar.getD (i + 1) 0 < i + 1) &&
      eAdj (cReps.getD (cPar.getD (i + 1) 0) 0) (cReps.getD (i + 1) 0)) &&
    allBelow 42 fun x => decide ((cWords.getD x (0, [])).1 < 6) &&
      (cWords.getD x (0, [])).2.all (· < 4) &&
      wordAt P (cWords.getD x (0, [])).2 (cReps.getD (cWords.getD x (0, [])).1 0) == x

@[expose] def centRSearch (P Z : Nat → Nat → Nat) : Bool :=
  (allBelow 6 fun k => eInv gTabs[k]!) && cDataOK P && cSearch P Z 6 []

@[expose] def centRCheck : Bool :=
  centRSearch (fun k y => (p0Gens[k]!)[y]!) (fun j x => (zRes[j]!)[x]!)

@[expose] def tauZCheck : Bool :=
  let y := conjTab 1782 tauT tauT ttabs[zI[2]!]!
  tFound y && tPos y == zI[3]! && !(comp 1782 tTab C1Model.zT == comp 1782 C1Model.zT tTab)

@[expose] def rhoACheck : Bool :=
  let idx := indexOf a4Enum.tabs
  ct0Tabs.all fun c =>
    let c2 := comp 1782 c c
    let u := conjTab 1782 c c2 w0T
    !(comp 1782 c c2 == idTab 1782 && !(c == idTab 1782) &&
        comp 1782 u w0T == comp 1782 w0T u && !(u == w0T) &&
        conjTab 1782 c c2 u == comp 1782 w0T u) ||
      found idx a4Enum.tabs c

end CFSG.Sporadic.SuzRecog.B0Gluing
