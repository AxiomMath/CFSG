module

public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.Kernel.L34W.Tab42
public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K

@[expose] noncomputable def bNot (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def bEq (a b : Bool) : Bool := bIf(a, b, bNot b)

@[expose] noncomputable def outI (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), false, bIf(Nat.beq i (nat_lit 25), false, bNot (Nat.beq i (nat_lit 31))))

@[expose] noncomputable def isOutK (Y : Nat → Nat) (n : Nat) : Bool :=
  bAnd(outI (Nat.div n (nat_lit 64)), invPt (nat_lit 42) (nat_lit 6) (Y n))

@[expose] noncomputable def yOK (G Y : Nat → Nat) : Bool :=
  allN (nat_lit 36) fun i => strictB (repK G i) fun r => allN (nat_lit 64) fun t =>
    Nat.beq (Y (Nat.add (Nat.mul (nat_lit 64) i) t)) (pcomp (nat_lit 42) (nat_lit 6) (mask 6) (tgK G t) r)

@[expose] noncomputable def outOK (Y OT RK : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 2304) fun n => strictB (RK n) fun r =>
      bIf(Nat.blt r (nat_lit 144), bAnd(Nat.beq (OT r) n, isOutK Y n), bNot (isOutK Y n)),
    allN (nat_lit 144) fun j => strictB (OT j) fun n =>
      bAnd(Nat.blt n (nat_lit 2304), Nat.beq (RK n) j))

@[expose] noncomputable def commOK (Y OT CM : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun j => strictB (Y (OT j)) fun y => strictB (CM j) fun c =>
    allN (nat_lit 144) fun j' => bEq (hasBit c j') (commPt (nat_lit 42) (nat_lit 6) y (Y (OT j')))

@[expose] noncomputable def betaOK (T A OT BT : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun j => strictB (OT j) fun n =>
    strictB (Nat.mul (nat_lit 16) (Nat.mod n (nat_lit 64))) fun g =>
    strictB (invC T g) fun gi => strictB (BT j) fun b =>
      allN (nat_lit 64) fun k =>
        Nat.beq (pg (nat_lit 10) (mask 10) b k) (betaW T A g gi (Nat.div n (nat_lit 64)) (Nat.mul (nat_lit 16) k))

@[expose] noncomputable def kvK (T BT : Nat → Nat) (j k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), true,
    bAnd(Nat.beq (Nat.div (mulC T (Nat.mul (nat_lit 16) k) (Nat.mul (nat_lit 16) k)) (nat_lit 16)) (nat_lit 0),
      Nat.beq (Nat.div (pg (nat_lit 10) (mask 10) (BT j) k) (nat_lit 16)) k))

end CFSG.KC.L34W

end
