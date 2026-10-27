module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.E27Lie

open CFSG.KC.Ord CFSG.KC.Enum

@[expose] noncomputable def treeC (mm : Nat → Nat → Nat) (key pp pj g : Nat → Nat) (one m i : Nat) :
    Bool :=
  bIf(Nat.beq i (nat_lit 0), Nat.beq (key (nat_lit 0)) one,
    strictB (pp i) fun p => strictB (pj i) fun j =>
      bAnd(Nat.blt p i, bAnd(Nat.blt j m, Nat.beq (key i) (mm (g j) (key p)))))

@[expose] noncomputable def leftC (mm : Nat → Nat → Nat) (key : Nat → Nat) (lt : Nat → Nat → Nat)
    (g : Nat → Nat) (n j i : Nat) : Bool :=
  strictB (lt j i) fun l => bAnd(Nat.blt l n, Nat.beq (key l) (mm (g j) (key i)))

@[expose] noncomputable def sortC (key s : Nat → Nat) (n q : Nat) : Bool :=
  strictB (s q) fun a => bAnd(Nat.blt a n,
    bIf(Nat.blt (Nat.succ q) n, strictB (s (Nat.succ q)) fun b => Nat.blt (key a) (key b), true))

@[expose] noncomputable def killC (mm : Nat → Nat → Nat) (key W CI REP : Nat → Nat) (n nr a : Nat) :
    Bool :=
  bIf(Nat.beq a (nat_lit 0), true,
    strictB (W a) fun w => strictB (CI a) fun c =>
      bAnd(Nat.blt w n, bAnd(Nat.blt c nr, strictB (REP c) fun r =>
        Nat.beq (mm (key w) (key a)) (mm (key r) (key w)))))

@[expose] noncomputable def repC (mm : Nat → Nat → Nat) (key REP CB : Nat → Nat)
    (cw : Nat → Nat → Nat) (one n k c : Nat) : Bool :=
  strictB (REP c) fun r => bAnd(Nat.blt r n, bIf(Nat.beq r (nat_lit 0), true,
    strictB (key r) fun X =>
      bIf(Nat.beq (CB c) (nat_lit 0), notB (Nat.beq (mm X (mm X X)) one),
        allN k fun t => strictB (cw c t) fun b => bAnd(Nat.blt b n,
          bAnd(bIf(Nat.beq t (nat_lit 0), true, Nat.blt (cw c (Nat.sub t (nat_lit 1))) b),
            strictB (key b) fun B => Nat.beq (mm B X) (mm X B))))))

@[expose] noncomputable def blkC (b n : Nat) (f : Nat → Bool) (q : Nat) : Bool :=
  allN b fun t => strictB (Nat.add (Nat.mul b q) t) fun i => bIf(Nat.blt i n, f i, true)

end CFSG.KC.E27Lie

end
