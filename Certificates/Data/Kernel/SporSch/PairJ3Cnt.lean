module

public import Certificates.Data.Kernel.SporSch.PairClT

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def eqOnL (bs : List Nat) (f g : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(Nat.beq (f b) (g b), ih)) bs

@[expose] noncomputable def powF (f : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => strictN y f) e

@[expose] noncomputable def ordPL (bs : List Nat) (f : Nat → Nat) (p : Nat) : Bool :=
  bAnd(eqOnL bs (powF f p) (fun x => x), bIf(eqOnL bs f (fun x => x), false, true))

@[expose] noncomputable def ord9L (bs : List Nat) (f : Nat → Nat) : Bool :=
  bAnd(eqOnL bs (powF f (nat_lit 9)) (fun x => x),
    bIf(eqOnL bs (powF f (nat_lit 3)) (fun x => x), false, true))

@[expose] noncomputable def nfValidK (nb : Nat) (LR : Nat → Nat) (F : Nat) : Bool :=
  allN nb (fun t => Nat.blt fld(F, Nat.mul (nat_lit 16) t, nat_lit 65535) (rcnt (LR t)))

@[expose] noncomputable def nf4 (k0 k1 k2 k3 : Nat) : Nat :=
  Nat.lor k0 (Nat.lor (Nat.shiftLeft k1 (nat_lit 16))
    (Nat.lor (Nat.shiftLeft k2 (nat_lit 32)) (Nat.shiftLeft k3 (nat_lit 48))))

@[expose] noncomputable def srchAt (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (k0 : Nat) : Nat :=
  strictN (trInvPtT w kS NR NL LT PT (nat_lit 0) k0 (Y (trPtT w NR NL LT PT (nat_lit 0) k0 b0)))
    (fun u => strictN (lvT NL w QT (nat_lit 1) u) (fun k1 =>
    nIf(Nat.blt k1 (rcnt (LR (nat_lit 1))),
      foldUp (rcnt (LR (nat_lit 2))) (fun k2 s => foldUp (rcnt (LR (nat_lit 3))) (fun k3 s =>
        strictN (nf4 k0 k1 k2 k3) (fun F =>
          nIf(eqOnL bs (fun b => nfPtT w NR NL LT PT (nat_lit 4) F (X b))
              (fun b => Y (nfPtT w NR NL LT PT (nat_lit 4) F b)), Nat.succ s, s))) s) (nat_lit 0),
      nat_lit 0)))

@[expose] noncomputable def srchR (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => srchAt w kS NR NL LT PT QT LR bs b0 X Y (Nat.add lo j))

@[expose] noncomputable def scanAt (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z : Nat → Nat) (i : Nat) : Nat :=
  nIf(Nat.blt i c, strictN (nfX (nat_lit 4) (X i)) (fun x =>
    nIf(bAnd(ordPL bs (fun b => nfPtT w NR NL LT PT (nat_lit 4) x (Z b)) (nat_lit 3),
        ord9L bs (fun b => Z (Z (nfPtT w NR NL LT PT (nat_lit 4) x (Z b))))),
      nat_lit 1, nat_lit 0)), nat_lit 0)

@[expose] noncomputable def scanR (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => scanAt w NR NL LT PT bs c X Z (Nat.add lo j))

@[expose] noncomputable def invAt (w NR NL : Nat) (LT PT LR : Nat → Nat) (bs : List Nat) (c : Nat)
    (X : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.blt i c, strictB (nfX (nat_lit 4) (X i)) (fun x =>
    bAnd(nfValidK (nat_lit 4) LR x, ordPL bs (nfPtT w NR NL LT PT (nat_lit 4) x) (nat_lit 2))), true)

@[expose] noncomputable def bindAt (n w NR NL : Nat) (LT PT : Nat → Nat) (F P x : Nat) : Bool :=
  bIf(Nat.blt x n, Nat.beq (pg w (mask w) P x) (nfPtT w NR NL LT PT (nat_lit 4) F x), true)

end CFSG.KS.SporSch

end
