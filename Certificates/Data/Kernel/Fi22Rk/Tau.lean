module

public import Certificates.Data.Kernel.Fi22Rk.Defs
public import Certificates.Data.Kernel.Fi22.Cent

public section

namespace CFSG.KC.Fi22Rk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Fi22Cent
open CFSG.KLie.CT (orB notB)

@[expose] noncomputable def tauAt (s b : Nat) : Bool :=
  strictB (pinvS (nat_lit 3510) (nat_lit 12) (mask 12) s) fun r =>
    strictB (pg (nat_lit 12) (mask 12) s b) fun v => bAnd(Nat.blt v (nat_lit 3510),
      allN (nat_lit 3510) fun x =>
        Nat.beq (pg (nat_lit 12) (mask 12) s (cK b (pg (nat_lit 12) (mask 12) r x))) (cK v x))

@[expose] noncomputable def chainAt (FC : Nat) (PK : Nat → Nat) (q : Nat) : Bool :=
  strictB (PK q) fun p => orB (Nat.beq p (nat_lit 0)) (strictB (Nat.sub p (nat_lit 1)) fun c =>
    strictB (pg (nat_lit 12) (mask 12) FC (Nat.add (Nat.mul (nat_lit 3) c) (nat_lit 1))) fun x =>
    strictB (pg (nat_lit 12) (mask 12) FC (Nat.add (Nat.mul (nat_lit 3) c) (nat_lit 2))) fun y =>
      bAnd(Nat.blt x (nat_lit 3510), bAnd(Nat.blt y (nat_lit 3510), bAnd(Nat.ble (PK x) c,
        bAnd(Nat.ble (PK y) c, Nat.beq (cK x y) q)))))

end CFSG.KC.Fi22Rk

end
