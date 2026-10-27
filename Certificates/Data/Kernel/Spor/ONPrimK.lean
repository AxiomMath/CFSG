module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.ONPrim

open CFSG.KC.Enum

@[expose] noncomputable def repOf (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), nat_lit 0, nIf(Nat.beq l (nat_lit 1), nat_lit 1,
    nIf(Nat.beq l (nat_lit 2), nat_lit 2, nIf(Nat.beq l (nat_lit 3), nat_lit 4, nat_lit 9))))

@[expose] noncomputable def labOf (r : Nat) : Nat := Nat.shiftRight r (nat_lit 24)

@[expose] noncomputable def primOK (TT UU : Nat → Nat → Nat) (R : Nat → Nat) (n y r : Nat) :
    Bool :=
  strictB (labOf r) fun l => strictB (fld(r, nat_lit 17, nat_lit 63)) fun d =>
    bAnd(Nat.blt l (nat_lit 5), bAnd(Nat.ble (repOf l) y,
      bIf(Nat.beq d (nat_lit 0),
        bAnd(Nat.beq (repOf l) y, bAnd(Nat.beq (labOf (R (UU (nat_lit 2) y))) l,
          Nat.beq (labOf (R (UU (nat_lit 3) y))) l)),
        strictB (fld(r, nat_lit 23, nat_lit 1)) fun g =>
          strictB (Nat.land r (nat_lit 131071)) fun p => bAnd(Nat.blt p n,
            strictB (R p) fun rp => bAnd(Nat.blt (fld(rp, nat_lit 17, nat_lit 63)) d,
              bAnd(Nat.beq (labOf rp) l, bAnd(Nat.beq (TT (Nat.add (nat_lit 2) g) p) y,
                Nat.beq (labOf (R (UU (Nat.sub (nat_lit 3) g) y))) l)))))))

@[expose] noncomputable def primAt (TT UU : Nat → Nat → Nat) (R : Nat → Nat) (n y : Nat) : Nat :=
  strictN (R y) fun r => nIf(primOK TT UU R n y r,
    Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 17) (labOf r)),
    Nat.shiftLeft (nat_lit 1) (nat_lit 85))

@[expose] noncomputable def primCnt (TT UU : Nat → Nat → Nat) (R : Nat → Nat) (n lo cnt : Nat) :
    Nat :=
  foldBlk lo (fun y s => Nat.add (primAt TT UU R n y) s) cnt (nat_lit 0)

@[expose] noncomputable def primBlk (TT UU : Nat → Nat → Nat) (R C : Nat → Nat) (n w s : Nat) :
    Bool :=
  Nat.beq (primCnt TT UU R n (Nat.mul w s) w) (C s)

@[expose] noncomputable def primSizesP : Nat :=
  Nat.add (nat_lit 1) (Nat.add (Nat.shiftLeft (nat_lit 6384) (nat_lit 17))
    (Nat.add (Nat.shiftLeft (nat_lit 52136) (nat_lit 34))
      (Nat.add (Nat.shiftLeft (nat_lit 58653) (nat_lit 51))
        (Nat.shiftLeft (nat_lit 5586) (nat_lit 68)))))

@[expose] noncomputable def primTot (C : Nat → Nat) (k : Nat) : Bool :=
  Nat.beq (foldBlk (nat_lit 0) (fun s t => Nat.add (C s) t) k (nat_lit 0)) primSizesP

@[expose] noncomputable def primHead (TT : Nat → Nat → Nat) : Bool :=
  bAnd(Nat.beq (TT (nat_lit 2) (nat_lit 0)) (nat_lit 0),
    Nat.beq (TT (nat_lit 3) (nat_lit 0)) (nat_lit 0))

end CFSG.KS.ONPrim

end
