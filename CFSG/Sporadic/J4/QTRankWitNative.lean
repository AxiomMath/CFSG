module

public import CFSG.Sporadic.J4.QTRankInvNative

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

inductive Ins : Type
  | mul (i j k : Nat) : Ins
  | pow (n i k : Nat) : Ins

@[expose] def runN (R : Nat → Array V2) : List Ins → (Nat → Array V2)
  | [] => R
  | .mul i j k :: p =>
      runN (fun r => if r = k then mulRows (R i) (R j) else R r) p
  | .pow n i k :: p =>
      runN (fun r => if r = k then powRows (R i) n else R r) p

@[expose] def prog11 : List Ins :=
  [.mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 3 6, .pow 4 3 7, .pow 8 6 8,
    .pow 32 8 9, .mul 9 7 10, .mul 10 8 11, .mul 0 11 12, .mul 12 11 13, .pow 3 13 14,
    .mul 12 12 15, .mul 14 15 16, .pow 6 12 17, .mul 17 16 18, .mul 0 18 19, .mul 19 0 20,
    .pow 39 18 21, .mul 20 21 22, .mul 21 21 23, .mul 23 21 24, .mul 24 0 25, .mul 25 18 26,
    .pow 1 0 27, .mul 26 27 28, .mul 28 18 29, .mul 29 18 30]

@[expose] def init11 (r : Nat) : Array V2 := if r = 0 then rowsA else if r = 1 then rowsB else idRows

@[expose] def regs11 (_ : Unit) : Nat → Array V2 := runN init11 prog11

@[expose] def wfRows (X : Array V2) : Bool := X.size == 112 && X.all V2.wf

@[expose] def X11 (_ : Unit) : Array V2 := regs11 () 22

@[expose] def Y11 (_ : Unit) : Array V2 := regs11 () 30

@[expose] def Z11 (_ : Unit) : Array V2 :=
  mulRows (mulRows (mulRows (X11 ()) (Y11 ())) (powRows (X11 ()) 10)) (powRows (Y11 ()) 10)

@[expose] def C37 (_ : Unit) : Array V2 :=
  let T := uTab (locMats ()) (locInvs ())
  let t := etaRT T 1
  let g := mulRows (mulRows (mulRows (mulRows (gMat 0) (gMat 1)) (gMat 0)) (gMat 1)) (gMat 0)
  let gi := mulRows (mulRows (mulRows (mulRows (gInv 0) (gInv 1)) (gInv 0)) (gInv 1)) (gInv 0)
  mulRows t (mulRows (mulRows gi t) g)

@[expose] def AE5 (_ : Unit) : Array V2 :=
  mulRows (gMat 0) (etaRT (uTab (locMats ()) (locInvs ())) 5)

end CFSG.Sporadic.J4.QT
