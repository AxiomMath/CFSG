module

public import Certificates.Data.CFSGNative.ExcCensus.Check

public section

open Std

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

inductive NbrW where
  | small (g : Nat) (L : List (Nat × Nat))
  | weyl (w : LinW) (L : List (Nat × Nat))
  deriving Inhabited

@[expose] def nbrWOK (T : Tabs) (m : Fin 6) (k : Nat) : NbrW → Bool
  | .small g L => decide (cardN (nroots m) g ≤ 2) && genOK T (nroots m) g k L
  | .weyl w L =>
    linOK T (nroots m) w && genOK T (nroots m) (nodeMask w fun _ => true) k L && notB2 m k

@[expose] def compsOK (T : Tabs) (r z : Nat) (ks : List Nat) : Bool :=
  ks.all (fun k => connN T r k && subN (trunc r k) z &&
      Nat.all r fun i _ => !k.testBit i || subN (T.adj[i]! &&& z) k) &&
    Nat.all r fun t _ => !z.testBit t || ks.any fun k => k.testBit t

structure NSearch where
  comps : Nat → List (Nat × NbrW)
  deriving Inhabited

@[expose] def nbrLineOK (T : Tabs) (m : Fin 6) (X : NSearch) (cv : Nat) : Bool :=
  compsOK T (nroots m) (T.zm[cv]!) ((X.comps cv).map Prod.fst) &&
    (X.comps cv).all fun e => nbrWOK T m e.1 e.2

@[expose] def nbrAllOK (m : Fin 6) (T : Tabs) (X : NSearch) : Bool :=
  tabsOK m T && Nat.all (3 ^ dim m) fun cv _ => cv == 0 || nbrLineOK T m X cv

def diffS (m : Fin 6) : Array (Array Nat) :=
  let m' : Fin 6 := if m.val = 3 then 2 else m
  let d := dim m'
  let r := nroots m
  let vecs : Array (Array Int) :=
    (Array.range r).map fun i => (Array.range d).map fun k => fN m' i k
  let ix : HashMap (Array Int) Nat := (Array.range r).foldl (fun acc i => acc.insert vecs[i]! i) {}
  vecs.map fun vi => vecs.map fun vj =>
    (ix[(Array.range d).map fun k => vi[k]! - vj[k]!]?).getD r

def simpleDS (D : Array (Array Nat)) (r c : Nat) : List Nat :=
  let ids := (bitsS r c).toList
  ids.filter fun i => !(ids.any fun j => j != i && (D[i]![j]! < r && c.testBit D[i]![j]!))

def compsS (T : Tabs) (r z : Nat) : List Nat := Id.run do
  let mut rest := trunc r z
  let mut out : Array Nat := #[]
  for _ in [0:r] do
    if rest != 0 then
      let C := compS T r rest
      out := out.push C
      rest := rest ^^^ C
  return out.toList

def leafS (tc n : Nat) : Nat := ((List.range (rkN tc n)).find? fun a => leafN tc n a).getD 0

def nbrWS (T : Tabs) (m : Fin 6) (D : Array (Array Nat)) (k : Nat) : Option NbrW :=
  let r := nroots m
  let ss := simpleDS D r k
  if ss.length ≤ 2 then
    let W := NbrW.small (maskS ss) (closureS T r ss).2
    if nbrWOK T m k W then some W else none
  else
    let V : Array (Nat × Bool) := (ss.map fun i => (i, false)).toArray
    match identifyS (cartanS T V) with
    | none => none
    | some (tc, n, π) =>
      let a := leafS tc n
      let w : LinW := { linS V tc n π 0 0 with a := a, b := if a == 0 then 1 else 0 }
      let W := NbrW.weyl w (closureS T r w.nodes).2
      if nbrWOK T m k W then some W else none

def nSearchOf (m : Fin 6) (T : Tabs) : NSearch :=
  let D := diffS m
  { comps := fun cv =>
      (compsS T (nroots m) (T.zm[cv]!)).filterMap fun k => (nbrWS T m D k).map fun W => (k, W) }

@[expose] def nbrCheck (m : Fin 6) : Bool :=
  let T := tabsOf m
  nbrAllOK m T (nSearchOf m T)

end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
