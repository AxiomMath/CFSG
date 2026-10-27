module

public import Certificates.Data.Kernel.Spor.Row

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btKey (kw km : Nat) (K : Nat → Nat) (i : Nat) : Nat :=
  rg kw km K (nat_lit 0) i

@[expose] noncomputable def btRec (R : Nat → Nat) (i : Nat) : Nat :=
  rg (nat_lit 64) (nat_lit 18446744073709551615) R (nat_lit 0) i

@[expose] noncomputable def btLab (r : Nat) : Nat := Nat.land r (nat_lit 255)

@[expose] noncomputable def btPar (r : Nat) : Nat := fld(r, nat_lit 8, nat_lit 4294967295)

@[expose] noncomputable def btDep (r : Nat) : Nat := Nat.shiftRight r (nat_lit 40)

@[expose] noncomputable def btPos (POS : Nat → Nat) (k i j : Nat) : Nat :=
  rg (nat_lit 32) (nat_lit 4294967295) POS (nat_lit 0) (Nat.add (Nat.mul i k) j)

@[expose] noncomputable def btMov (w m d g x y : Nat) : Bool :=
  allN d (fun t => Nat.beq (pg w m y t) (pg w m g (pg w m x t)))

@[expose] noncomputable def btCanon (n w m d x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x (Nat.mul w d)) (nat_lit 0),
    allN d (fun t => Nat.blt (pg w m x t) n))

@[expose] noncomputable def btHdK (cnt : Nat) : Bool := Nat.blt (nat_lit 0) cnt

@[expose] noncomputable def btPtK (n w m d kw km k cnt base : Nat) (G K R POS : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (btKey kw km K i) (fun x =>
  strictB (btRec R i) (fun r =>
  bAnd(btCanon n w m d x,
  bAnd(bIf(Nat.blt (Nat.succ i) cnt, Nat.blt x (btKey kw km K (Nat.succ i)), true),
  bAnd(bIf(Nat.beq (btDep r) (nat_lit 0), Nat.beq x base,
    strictB (btPar r) (fun p => strictB (btLab r) (fun l =>
      bAnd(Nat.blt p cnt, bAnd(Nat.blt l k,
        bAnd(Nat.beq (Nat.succ (btDep (btRec R p))) (btDep r),
          btMov w m d (G l) (btKey kw km K p) x)))))),
  allN k (fun j => strictB (btPos POS k i j) (fun q =>
    bAnd(Nat.blt q cnt, btMov w m d (G j) x (btKey kw km K q)))))
  ))))

@[expose] noncomputable def btSlK (n w m d kw km k cnt base : Nat) (G K R POS : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun e => strictB (Nat.add lo e) (fun i =>
    bIf(Nat.blt i cnt, btPtK n w m d kw km k cnt base G K R POS i, true)))

end CFSG.KS.BTup

end
