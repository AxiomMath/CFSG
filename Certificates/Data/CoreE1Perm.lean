module

public import Certificates.Data.FusD2Perm

public section

namespace Certificates.CoreE1Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

structure Nrm where
  two : Bool
  a : Nat
  b : Nat
  α : Nat
  β : Nat
  γ : Nat
  δ : Nat
deriving Inhabited

structure Entry where
  move : Bool
  gWs : List (List Int)
  nd : List Nrm
  hW : List Int
  m : Nat
  tWs : List (List Int)
deriving Inhabited

structure Data where
  n : Nat
  aT : Tab
  bT : Tab
  sW : List (List Int)
  zW : List Int
  xWs : List (List Int)
  es : List Entry
deriving Inhabited

@[expose] def gsT (D : Data) : Array Tab := #[D.aT, D.bT]

@[expose] def giT (D : Data) : Array Tab := (gsT D).map (invTab D.n)

@[expose] def wT (D : Data) (w : List Int) : Tab := wordT D.n (gsT D) (giT D) w

@[expose] def sGens (D : Data) : Array Tab := (D.sW.map (wT D)).toArray

@[expose] def sEnum (D : Data) : Enum := enumBFS D.n (sGens D) 27

@[expose] def zT (D : Data) : Tab := wT D D.zW

@[expose] def xT (D : Data) (i : Nat) : Tab := wT D (D.xWs.getD i [])

@[expose] def zx (D : Data) (i a b : Nat) : Tab :=
  comp D.n (powT D.n (zT D) a) (powT D.n (xT D i) b)

@[expose] def central (D : Data) (t : Tab) : Bool :=
  (sGens D).all fun s => comp D.n t s == comp D.n s t

@[expose] def inZ (D : Data) (t : Tab) : Bool := anyBelow 3 fun a => t == powT D.n (zT D) a

@[expose] def inE (D : Data) (i : Nat) (t : Tab) : Bool :=
  anyBelow 3 fun a => anyBelow 3 fun b => t == zx D i a b

@[expose] def gensOK (D : Data) : Bool :=
  allBelow 2 fun j => (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! (gsT D)[j]! == idTab D.n

@[expose] def sOK (D : Data) : Bool :=
  enumOK D.n (sGens D) (sEnum D) && (sEnum D).tabs.size == 27 &&
    (sGens D).any fun s => (sGens D).any fun t => !(comp D.n s t == comp D.n t s)

@[expose] def zOK (D : Data) : Bool :=
  (sEnum D).tabs.contains (zT D) && !(zT D == idTab D.n) && powT D.n (zT D) 3 == idTab D.n &&
    central D (zT D) && (sEnum D).tabs.all fun t => !(central D t) || inZ D t

@[expose] def xOK (D : Data) : Bool :=
  (allBelow D.xWs.length fun i => (sEnum D).tabs.contains (xT D i) &&
      powT D.n (xT D i) 3 == idTab D.n && comp D.n (xT D i) (zT D) == comp D.n (zT D) (xT D i) &&
      !(inZ D (xT D i))) &&
    (sEnum D).tabs.all fun t => anyBelow D.xWs.length fun i => inE D i t

@[expose] def gT (D : Data) (e : Entry) : Array Tab := (e.gWs.map (wT D)).toArray

@[expose] def gTi (D : Data) (e : Entry) : Array Tab := (gT D e).map (invTab D.n)

@[expose] def nrmOK (D : Data) (i : Nat) (g : Tab) (f : Nrm) : Bool :=
  if f.two then
    comp D.n g (zT D) == comp D.n (zx D i f.α f.β) g &&
      comp D.n g (xT D i) == comp D.n (zx D i f.γ f.δ) g
  else
    !(zx D i f.a f.b == idTab D.n) &&
      comp D.n g (zx D i f.a f.b) == comp D.n (powT D.n (zx D i f.a f.b) f.α) g

@[expose] def moveOK (D : Data) (e : Entry) : Bool :=
  let h := wordT D.n (gT D e) (gTi D e) e.hW
  let hi := invTab D.n h
  let c := comp D.n (zT D) (comp D.n (comp D.n h (zT D)) hi)
  hi.size == D.n && comp D.n hi h == idTab D.n && !(c == idTab D.n) &&
    powT D.n c e.m == idTab D.n && !(e.m % 3 == 0)

@[expose] def transOK (D : Data) (i : Nat) (e : Entry) : Bool :=
  e.nd.all (fun f => f.two) && e.tWs.length == 9 &&
    allBelow 9 fun k => k == 0 ||
      let w := wordT D.n (gT D e) (gTi D e) (e.tWs.getD k [])
      comp D.n w (zT D) == comp D.n (zx D i (k / 3) (k % 3)) w

@[expose] def entryOK (D : Data) (i : Nat) (e : Entry) : Bool :=
  (allBelow (gT D e).size fun j => (gTi D e)[j]!.size == D.n &&
      comp D.n (gTi D e)[j]! (gT D e)[j]! == idTab D.n &&
      nrmOK D i (gT D e)[j]! (e.nd.getD j default)) &&
    e.nd.length == e.gWs.length && (if e.move then moveOK D e else transOK D i e)

@[expose] def check (D : Data) : Bool :=
  gensOK D && sOK D && zOK D && xOK D && D.es.length == D.xWs.length &&
    allBelow D.es.length fun i => entryOK D i (D.es.getD i default)

end Certificates.CoreE1Perm
