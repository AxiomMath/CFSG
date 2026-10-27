module

public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace Certificates.FusD2Perm

open CFSG.PSL3Four.Native

@[expose] def powT (n : Nat) (t : Tab) : Nat → Tab
  | 0 => idTab n
  | k + 1 => comp n t (powT n t k)

@[expose] def wordT (n : Nat) (gs gi : Array Tab) : List Int → Tab
  | [] => idTab n
  | z :: w =>
    comp n (if 0 < z then gs.getD (z.toNat - 1) (idTab n) else gi.getD ((-z).toNat - 1) (idTab n))
      (wordT n gs gi w)

structure Data where
  n : Nat
  p : Nat
  aT : Tab
  bT : Tab
  xW : List Int
  yW : List Int
  gWs : List (List Int)
  fd : List (Nat × Nat × Nat × Nat)
  wA : List Int
  wB : List Int
deriving Inhabited

@[expose] def gsT (D : Data) : Array Tab := #[D.aT, D.bT]

@[expose] def giT (D : Data) : Array Tab := (gsT D).map (invTab D.n)

@[expose] def xT (D : Data) : Tab := wordT D.n (gsT D) (giT D) D.xW

@[expose] def yT (D : Data) : Tab := wordT D.n (gsT D) (giT D) D.yW

@[expose] def gT (D : Data) : Array Tab := (D.gWs.map (wordT D.n (gsT D) (giT D))).toArray

@[expose] def gTi (D : Data) : Array Tab := (gT D).map (invTab D.n)

@[expose] def fusPair (D : Data) (d : Nat × Nat × Nat × Nat) : Tab × Tab :=
  (comp D.n (powT D.n (xT D) d.1) (powT D.n (yT D) d.2.1),
    comp D.n (powT D.n (xT D) d.2.2.1) (powT D.n (yT D) d.2.2.2))

@[expose] def fusOK (D : Data) : Bool :=
  allBelow (gT D).size fun j =>
    let uw := fusPair D (D.fd.getD j (0, 0, 0, 0))
    !(uw.1 == idTab D.n) && comp D.n (gT D)[j]! uw.1 == comp D.n uw.2 (gT D)[j]!

@[expose] def check (D : Data) : Bool :=
  (allBelow 2 fun j => (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! (gsT D)[j]! == idTab D.n) &&
    (allBelow (gT D).size fun j =>
      (gTi D)[j]!.size == D.n && comp D.n (gTi D)[j]! (gT D)[j]! == idTab D.n) &&
    powT D.n (xT D) D.p == idTab D.n && powT D.n (yT D) D.p == idTab D.n &&
    comp D.n (xT D) (yT D) == comp D.n (yT D) (xT D) && !(xT D == idTab D.n) &&
    D.fd.length == D.gWs.length && fusOK D &&
    wordT D.n (gT D) (gTi D) D.wA == D.aT && wordT D.n (gT D) (gTi D) D.wB == D.bT

end Certificates.FusD2Perm
