module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.Co1T

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def tu (PT k : Nat) : Nat :=
  pg (nat_lit 24) (mask (nat_lit 24)) PT (Nat.mul (nat_lit 2) k)

@[expose] noncomputable def tv (PT k : Nat) : Nat :=
  pg (nat_lit 24) (mask (nat_lit 24)) PT (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1))

@[expose] noncomputable def trisPK (PT : Nat) (L : List (Nat × Nat)) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih k => strictB k fun k =>
      bAnd(Nat.beq (tu PT k) p.1, bAnd(Nat.beq (tv PT k) p.2, ih (Nat.succ k)))) L k

@[expose] noncomputable def inTK (PT j a : Nat) : Bool :=
  strictB (tu PT j) fun u => strictB (tv PT j) fun v =>
    bIf(Nat.beq a u, true, bIf(Nat.beq a v, true, Nat.beq a (Nat.xor u v)))

@[expose] noncomputable def triOneK (T PT P k : Nat) : Bool :=
  bIf(Nat.blt k (nat_lit 1365),
    strictB (pg (nat_lit 11) (mask (nat_lit 11)) P k) fun j =>
    strictB (tu PT k) fun u => strictB (tv PT k) fun v =>
      bAnd(Nat.blt j (nat_lit 1365),
        bAnd(inTK PT j (CFSG.KC.M1F2.vmF (nat_lit 24) T u),
          bAnd(inTK PT j (CFSG.KC.M1F2.vmF (nat_lit 24) T v),
            inTK PT j (CFSG.KC.M1F2.vmF (nat_lit 24) T (Nat.xor u v))))),
    true)

@[expose] noncomputable def triWK (T PT P b len : Nat) : Bool := allBlk b (triOneK T PT P) len

@[expose] noncomputable def rkOK (SV SG ST i x : Nat) : Bool :=
  strictB (pg (nat_lit 12) (mask (nat_lit 12)) SG i) fun r =>
    bAnd(Nat.blt r (nat_lit 4095),
      bAnd(Nat.beq (pg (nat_lit 24) (mask (nat_lit 24)) SV r) x,
        Nat.beq (pg (nat_lit 12) (mask (nat_lit 12)) ST r) i))

@[expose] noncomputable def vecOK (TA SV SG ST i x : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) x,
    bAnd(Nat.beq (CFSG.KC.M1F2.vmF (nat_lit 24) TA x) x, rkOK SV SG ST i x))

@[expose] noncomputable def baseOneK (TA PT SV SG ST k : Nat) : Bool :=
  bIf(Nat.blt k (nat_lit 1365),
    strictB (tu PT k) fun u => strictB (tv PT k) fun v =>
      bAnd(vecOK TA SV SG ST (Nat.mul (nat_lit 3) k) u,
        bAnd(vecOK TA SV SG ST (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 1)) v,
          vecOK TA SV SG ST (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 2)) (Nat.xor u v))),
    true)

@[expose] noncomputable def baseK (TA PT SV SG ST b len : Nat) : Bool :=
  allBlk b (baseOneK TA PT SV SG ST) len

@[expose] noncomputable def sortK (SV n : Nat) : Bool :=
  allN n fun p => Nat.blt (pg (nat_lit 24) (mask (nat_lit 24)) SV p)
    (pg (nat_lit 24) (mask (nat_lit 24)) SV (Nat.succ p))

@[expose] noncomputable def mpowK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ ih => strictN ih fun q => CFSG.KS.SporSch.M24.mulK q X) e

@[expose] noncomputable def ne1K (T v : Nat) : Bool :=
  bIf(Nat.beq (CFSG.KC.M1F2.vmF (nat_lit 24) T v) v, false, true)

@[expose] noncomputable def neK2 (T T' v : Nat) : Bool :=
  bIf(Nat.beq (CFSG.KC.M1F2.vmF (nat_lit 24) T v) (CFSG.KC.M1F2.vmF (nat_lit 24) T' v), false, true)

@[expose] noncomputable def ne1K2 (T T' v : Nat) : Bool :=
  bIf(Nat.beq (CFSG.KC.M1F2.vmF (nat_lit 24) T (CFSG.KC.M1F2.vmF (nat_lit 24) T' v)) v, false, true)

end CFSG.KC.Co1T

end
