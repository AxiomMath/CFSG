module

public import Certificates.Data.FusD2Perm

public section

namespace Certificates.CoreD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

structure Fus where
  pair : Nat
  α : Nat
  β : Nat
  γ : Nat
  δ : Nat
deriving Inhabited

structure Data where
  n : Nat
  p : Nat
  aT : Tab
  bT : Tab
  eW : List (List Int)
  eK : Nat
  pairs : List (Nat × Nat)
  gWs : List (List Int)
  fd : List Fus
  wA : List Int
  wB : List Int
deriving Inhabited

@[expose] def gsT (D : Data) : Array Tab := #[D.aT, D.bT]

@[expose] def giT (D : Data) : Array Tab := (gsT D).map (invTab D.n)

@[expose] def wT (D : Data) (w : List Int) : Tab := wordT D.n (gsT D) (giT D) w

@[expose] def eGens (D : Data) : Array Tab := (D.eW.map (wT D)).toArray

@[expose] def eEnum (D : Data) : Enum := enumBFS D.n (eGens D) (D.p ^ D.eK)

@[expose] def eT (D : Data) (k : Nat) : Tab := (eGens D).getD k (idTab D.n)

@[expose] def gT (D : Data) : Array Tab := (D.gWs.map (wT D)).toArray

@[expose] def gTi (D : Data) : Array Tab := (gT D).map (invTab D.n)

@[expose] def pairOK (D : Data) (q : Nat × Nat) : Bool :=
  decide (q.1 < D.eW.length) && decide (q.2 < D.eW.length) &&
    powT D.n (eT D q.1) D.p == idTab D.n && powT D.n (eT D q.2) D.p == idTab D.n &&
    comp D.n (eT D q.1) (eT D q.2) == comp D.n (eT D q.2) (eT D q.1) &&
    !(eT D q.1 == idTab D.n) && allBelow D.p fun j => !(eT D q.2 == powT D.n (eT D q.1) j)

@[expose] def fusOK (D : Data) : Bool :=
  allBelow (gT D).size fun j =>
    let f := D.fd.getD j default
    let u := eT D (D.pairs.getD f.pair (0, 0)).1
    let v := eT D (D.pairs.getD f.pair (0, 0)).2
    decide (f.pair < D.pairs.length) &&
      comp D.n (gT D)[j]! u == comp D.n (comp D.n (powT D.n u f.α) (powT D.n v f.β)) (gT D)[j]! &&
      comp D.n (gT D)[j]! v == comp D.n (comp D.n (powT D.n u f.γ) (powT D.n v f.δ)) (gT D)[j]!

@[expose] def check (D : Data) : Bool :=
  (allBelow 2 fun j => (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! (gsT D)[j]! == idTab D.n) &&
    (allBelow (gT D).size fun j =>
      (gTi D)[j]!.size == D.n && comp D.n (gTi D)[j]! (gT D)[j]! == idTab D.n) &&
    enumOK D.n (eGens D) (eEnum D) && (eEnum D).tabs.size == D.p ^ D.eK &&
    D.pairs.all (pairOK D) && D.fd.length == D.gWs.length && fusOK D &&
    wordT D.n (gT D) (gTi D) D.wA == D.aT && wordT D.n (gT D) (gTi D) D.wB == D.bT

end Certificates.CoreD2Perm
