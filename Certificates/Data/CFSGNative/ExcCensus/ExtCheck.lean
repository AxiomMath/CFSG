module

public import Certificates.Data.CFSGNative.ExcCensus.Check
public import Certificates.Data.CFSGNative.ExcCensus.ExtCore

public section

open Std

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

def leafNode (tc n : Nat) : Nat := ((List.range (rkN tc n)).find? fun a => leafN tc n a).getD 0

def subTabOf (m : Fin 6) (ix : HashMap (Array Int) Nat) : Array (Array Nat) :=
  let m' : Fin 6 := if m.val = 3 then 2 else m
  let d := dim m'
  let r := nroots m
  let vs : Array (Array Int) := (Array.range r).map fun i => (Array.range d).map fun k => fN m' i k
  (Array.range r).map fun i => (Array.range r).map fun j =>
    match ix[(Array.range d).map fun k => vs[i]![k]! - vs[j]![k]!]? with
    | some t => t
    | none => r

def simpleT (st : Array (Array Nat)) (r c : Nat) : List Nat :=
  let ids := (bitsS r c).toList
  ids.filter fun i => !(ids.any fun j => j != i && (st[i]![j]! < r && c.testBit (st[i]![j]!)))

def nbrS (T : Tabs) (m : Fin 6) (st : Array (Array Nat)) (cz : Nat) :
    Option (LinW × List (Nat × Nat) × Array (Array Int)) :=
  let d := dim m
  let r := nroots m
  let k := T.zm[cz]!
  let ss := simpleT st r k
  let V : Array (Nat × Bool) := (ss.map fun i => (i, false)).toArray
  match identifyS (cartanS T V) with
  | none => none
  | some (tc, n, π) =>
    let a := leafNode tc n
    let w : LinW := { linS V tc n π 0 0 with a := a, b := if a == 0 then 1 else 0 }
    let L := (closureS T r w.nodes).2
    let B := lineB T d (nodeList w fun _ => true) cz
    if nbrOK T m cz k w L B then some (w, L, B) else none

def nbrWitS (T : Tabs) (m : Fin 6) (st : Array (Array Nat)) (cz : Nat) : Option ExtWit :=
  match nbrS T m st cz with
  | none => none
  | some (w, L, B) =>
    let rk := rkN w.tc w.n
    let Cm : Array (Array Int) :=
      (Array.range rk).map fun i => (Array.range rk).map fun j => cartanN w.tc w.n i j
    let inner : Option ExtWit :=
      match inv3 Cm rk with
      | none => none
      | some Bi =>
        if innerTypeN w.tc w.n && invOK rk (cartanN w.tc w.n) Bi then some (.inner w L B Bi)
        else none
    match inner with
    | some wit => some wit
    | none =>
      let rowsM : Array (Array Nat) :=
        (Array.range rk).map fun i => (Array.range rk).map fun j => m3 (cartanN w.tc w.n i j)
      match (null3 rowsM rk)[0]? with
      | none => none
      | some x =>
        let xi : Array Int := x.map fun (v : Nat) => (v : Int)
        if singOK rk (cartanN w.tc w.n) xi && detCondN T (dim m) w none then
          some (.det w L B xi none)
        else none

def ambFindS {α : Type} (T : Tabs) (m : Fin 6) (st : Array (Array Nat)) (cv cz : Nat)
    (sel : AmbW → Option α) : Option α :=
  let d := dim m
  let r := nroots m
  let ℓ := T.zm[cv]!
  let k := T.zm[cz]!
  let j := ℓ &&& k
  let (psi, Lpsi) := closureS T r (bitsS r (trunc r ℓ ||| trunc r k)).toList
  let ss := simpleT st r j
  if ss.length + 2 != d then none else
  (extsS T r ss j k).findSome? fun b' =>
    (bitsS r (psi ^^^ (psi &&& k))).toList.findSome? fun i =>
      [false, true].findSome? fun sg =>
        let V : Array (Nat × Bool) := (ss.map fun t => (t, false)).toArray ++ #[b', (i, sg)]
        match identifyS (cartanS T V) with
        | none => none
        | some (tc, n, π) =>
          let w := linS V tc n π (V.size - 1) (V.size - 2)
          let rk := rkN tc n
          let offA := nodeList w fun t => t != w.a
          let Hm : Array (Array Int) := (Array.range rk).map fun t => T.h[nodeN w t]!
          let W : AmbW :=
            { w, Lk := (closureS T r offA).2, La := Lpsi, Bk := lineB T d offA cz,
              Bb := (inv3 Hm rk).getD #[] }
          if ambOK T m cv cz ℓ k W then sel W else none

def ambDS (T : Tabs) (m : Fin 6) (st : Array (Array Nat)) (cv cz : Nat) :
    Option (AmbW × List Nat × Nat) :=
  ambFindS T m st cv cz fun W =>
    let rk := rkN W.w.tc W.w.n
    let Csub : Array (Array Int) := (Array.range (rk - 1)).map fun p =>
      (Array.range (rk - 1)).map fun q =>
        cartanN W.w.tc W.w.n (offN W.w.a p) (offN W.w.a q)
    match identifyS Csub with
    | some (3, _, π') =>
      let perm := π'.toList.map fun x => offN W.w.a x
      let h := (rk - 1) / 2
      if ambDOK T m cv cz (T.zm[cv]!) (T.zm[cz]!) W perm h then some (W, perm, h) else none
    | _ => none

def d5S (T : Tabs) (m : Fin 6) (st : Array (Array Nat)) (cv cz : Nat) :
    Option (AmbW × List (Nat × Nat)) :=
  let j := T.zm[cv]! &&& T.zm[cz]!
  ambFindS T m st cv cz fun W =>
    let Lj := (closureS T (nroots m) (nodeList W.w fun t => t != W.w.a && t != W.w.b)).2
    if d5OK T m cv cz (T.zm[cv]!) j (T.zm[cz]!) W Lj then some (W, Lj) else none

def leafW (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (cv cz : Nat) : ExtWit :=
  match modelS T m ix true cv cz with
  | some W => .leaf W
  | none => .twoL

def extX (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (st : Array (Array Nat))
    (tab : Array (Thunk (Option ExtWit))) (cv cy a b : Nat) : ExtWit :=
  let d := dim m
  let cz := combN d cv cy a b
  match (tab[cz]!).get with
  | some wit => wit
  | none =>
    let ℓ := T.zm[cv]!
    let j := ℓ &&& T.zm[cy]!
    let k := T.zm[cz]!
    if twoNodeN (labelOf T m ℓ) (labelOf T m j) then .twoL
    else if twoNodeN (labelOf T m k) (labelOf T m j) then .twoK
    else if d == 5 then
      match d5S T m st cv cz with
      | some (W, Lj) => .d5 W Lj
      | none => leafW T m ix cv cz
    else if d % 2 == 1 && 7 ≤ d then
      match ambDS T m st cv cz with
      | some (W, perm, h) => .ambD W perm h
      | none => leafW T m ix cv cz
    else leafW T m ix cv cz

@[noinline] def nbrTab (T : Tabs) (m : Fin 6) (st : Array (Array Nat)) :
    Array (Thunk (Option ExtWit)) :=
  (Array.range (3 ^ dim m)).map fun cz => Thunk.mk fun _ => nbrWitS T m st cz

@[expose, noinline] def extScanOn (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat)
    (st : Array (Array Nat)) (tab : Array (Thunk (Option ExtWit))) (lo n : Nat) : Bool :=
  extRangeOK T m (searchS T m true true) (extX T m ix st tab) lo n

@[expose] def extRangeCheck (m : Fin 6) (lo n : Nat) : Bool :=
  let T := tabsOf m
  let ix := rootIdx m
  let st := subTabOf m ix
  tabsOK m T && extScanOn T m ix st (nbrTab T m st) lo n

end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
