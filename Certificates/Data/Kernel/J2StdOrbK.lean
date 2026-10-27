module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.J2StdOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def f9 (P i : Nat) : Nat := fld(P, Nat.mul (nat_lit 9) i, nat_lit 511)

@[expose] noncomputable def trK (LR T : Nat → Nat) (i k : Nat) : Nat :=
  T (Nat.add (roff (nat_lit 315) (nat_lit 2835) (LR i)) k)

@[expose] noncomputable def cAt (A B C AI BI CI X p : Nat) : Nat :=
  f9 A (f9 B (f9 C (f9 X (f9 CI (f9 BI (f9 AI p))))))

@[expose] noncomputable def key3 (A B C AI BI CI X : Nat) : Nat :=
  Nat.add (cAt A B C AI BI CI X (nat_lit 0)) (Nat.mul (nat_lit 512)
    (Nat.add (cAt A B C AI BI CI X (nat_lit 4)) (Nat.mul (nat_lit 512)
      (cAt A B C AI BI CI X (nat_lit 3)))))

@[expose] noncomputable def keyC (LR TR TRI : Nat → Nat) (X a b c : Nat) : Nat :=
  key3 (trK LR TR (nat_lit 0) a) (trK LR TR (nat_lit 1) b) (trK LR TR (nat_lit 2) c)
    (trK LR TRI (nat_lit 0) a) (trK LR TRI (nat_lit 1) b) (trK LR TRI (nat_lit 2) c) X

@[expose] noncomputable def keyW1 (LR TR TRI : Nat → Nat) (X w : Nat) : Nat :=
  keyC LR TR TRI X (Nat.div w (nat_lit 1920)) (Nat.mod (Nat.div w (nat_lit 12)) (nat_lit 160))
    (Nat.mod w (nat_lit 12))

@[expose] noncomputable def keyW2 (LR TR TRI : Nat → Nat) (X Y w : Nat) : Nat :=
  Nat.add (keyW1 LR TR TRI X w) (Nat.mul (nat_lit 134217728) (keyW1 LR TR TRI Y w))

@[expose] noncomputable def stepQ (K : Nat → Nat) (B q x : Nat) : Nat :=
  nIf(Nat.beq q (nat_lit 0), nat_lit 0, strictN (K x) (fun k =>
    nIf(bAnd(Nat.blt x B, Nat.ble q (Nat.succ k)), Nat.succ (Nat.succ k), nat_lit 0)))

@[expose] noncomputable def foldQ (K : Nat → Nat) (B q : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun x _ ih q => strictN (stepQ K B q x) ih) L q

@[expose] noncomputable def lastL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x t ih => List.rec (motive := fun _ => Nat) x (fun _ _ _ => ih) t) L

@[expose] noncomputable def getL (Ls : List (Array Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih c => Nat.rec (motive := fun _ => List Nat) x.toList (fun c' _ => ih c') c) Ls

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s) (fun _ _ ih s => strictN (Nat.succ s) ih) L
    (nat_lit 0)

@[expose] noncomputable def lenLs (Ls : List (Array Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.add (lenL x.toList) ih) Ls

@[expose] noncomputable def consB (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) L

@[expose] noncomputable def qOf (K : Nat → Nat) (L : List Nat) : Nat :=
  Nat.succ (Nat.succ (K (lastL L)))

@[expose] noncomputable def qPrev (K : Nat → Nat) (Ls : List (Array Nat)) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun c' _ => qOf K (getL Ls c')) c

@[expose] noncomputable def chunkOK (K : Nat → Nat) (B : Nat) (Ls : List (Array Nat)) (c : Nat) :
    Bool :=
  bAnd(consB (getL Ls c), Bool.not (Nat.beq (foldQ K B (qPrev K Ls c) (getL Ls c)) (nat_lit 0)))

end CFSG.KC.J2StdOrb

end
