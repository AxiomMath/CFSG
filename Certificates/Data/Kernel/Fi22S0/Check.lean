module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.SporCov.BaseFix

public section

namespace CFSG.KC.Fi22S0

open CFSG.KC.Loop CFSG.KC.Enum CFSG.KC.SporCov

@[expose] noncomputable def ent (P x : Nat) : Nat := fld(P, Nat.mul (nat_lit 12) x, nat_lit 4095)

@[expose] noncomputable def compOK (P Q R : Nat) : Bool :=
  allBelow (nat_lit 3510) (nat_lit 55) fun x => Nat.beq (ent P x) (ent Q (ent R x))

@[expose] noncomputable def regC (RF oi oj : Nat → Nat) (k : Nat) : Bool :=
  strictB (oi k) fun i => strictB (oj k) fun j =>
    bAnd(Nat.blt i k, bAnd(Nat.blt j k, compOK (RF k) (RF i) (RF j)))

@[expose] noncomputable def baseC (RF A B : Nat → Nat) : Bool :=
  bAnd(agB (ent (RF (nat_lit 0))) A (nat_lit 3510) (nat_lit 55),
    bAnd(agB (ent (RF (nat_lit 1))) B (nat_lit 3510) (nat_lit 55),
      invB (ent (RF (nat_lit 1))) (ent (RF (nat_lit 2))) (nat_lit 3510) (nat_lit 55)))

@[expose] noncomputable def mapK (P K : Nat) : Nat :=
  Nat.lor (ent P fld(K, nat_lit 0, nat_lit 4095))
    (Nat.lor (Nat.shiftLeft (ent P fld(K, nat_lit 12, nat_lit 4095)) (nat_lit 12))
      (Nat.lor (Nat.shiftLeft (ent P fld(K, nat_lit 24, nat_lit 4095)) (nat_lit 24))
        (Nat.lor (Nat.shiftLeft (ent P fld(K, nat_lit 36, nat_lit 4095)) (nat_lit 36))
          (Nat.shiftLeft (ent P fld(K, nat_lit 48, nat_lit 4095)) (nat_lit 48)))))

@[expose] noncomputable def treeC (key pp pj g : Nat → Nat) (k0 i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), Nat.beq (key (nat_lit 0)) k0,
    strictB (pp i) fun p => strictB (pj i) fun j =>
      bAnd(Nat.blt p i, bAnd(Nat.blt j (nat_lit 3), Nat.beq (key i) (mapK (g j) (key p)))))

@[expose] noncomputable def leftC (key : Nat → Nat) (L : Nat → Nat → Nat) (g : Nat → Nat)
    (n j i : Nat) : Bool :=
  strictB (L j i) fun l => bAnd(Nat.blt l n, Nat.beq (key l) (mapK (g j) (key i)))

@[expose] noncomputable def sortC (key s : Nat → Nat) (n m : Nat) : Bool :=
  strictB (s m) fun a => bAnd(Nat.blt a n,
    bIf(Nat.blt (Nat.succ m) n, strictB (s (Nat.succ m)) fun b => Nat.blt (key a) (key b), true))

@[expose] noncomputable def blkC (b : Nat) (f : Nat → Bool) (q : Nat) : Bool :=
  allN b fun t => f (Nat.add (Nat.mul b q) t)

end CFSG.KC.Fi22S0

end
