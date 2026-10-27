module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.E27Orth

open CFSG.KC.Enum

@[expose] noncomputable def cnF2 (n x : Nat) : Bool := Nat.blt x (Nat.shiftLeft (nat_lit 1) (Nat.mul n n))

@[expose] noncomputable def baseI (cn : Nat → Bool) (one m : Nat) (G : Nat → Nat) : Bool :=
  bAnd(cn one, allN m fun j => cn (G j))

@[expose] noncomputable def treeI (mul : Nat → Nat → Nat) (cn : Nat → Bool) (one m : Nat)
    (G E Tr : Nat → Nat) (i : Nat) : Bool :=
  strictB (E i) fun x => bAnd(cn x, bIf(Nat.beq i (nat_lit 0), Nat.beq x one,
    strictB (Tr i) fun t => strictB (Nat.shiftRight t (nat_lit 4)) fun p =>
      strictB (Nat.land t (nat_lit 15)) fun j =>
        bAnd(Nat.blt p i, bAnd(Nat.blt j m, Nat.beq x (mul (G j) (E p))))))

@[expose] noncomputable def leftI (mul : Nat → Nat → Nat) (N : Nat) (G E Lf : Nat → Nat)
    (q : Nat) : Bool :=
  strictB (Lf q) fun k => bAnd(Nat.blt k N,
    Nat.beq (mul (G (Nat.div q N)) (E (Nat.mod q N))) (E k))

@[expose] noncomputable def keyI (N : Nat) (E S : Nat → Nat) (k : Nat) : Bool :=
  strictB (S k) fun s => bAnd(Nat.blt s N,
    bIf(Nat.blt (Nat.succ k) N, Nat.blt (E s) (E (S (Nat.succ k))), true))

@[expose] noncomputable def conjI (mul : Nat → Nat → Nat) (N nR : Nat) (E Rp W : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (W i) fun t => strictB (Nat.shiftRight t (nat_lit 16)) fun w =>
    strictB (Nat.land t (nat_lit 65535)) fun r => bAnd(Nat.blt w N, bAnd(Nat.blt r nR,
      Nat.beq (mul (E w) (E i)) (mul (E (Rp r)) (E w))))

@[expose] noncomputable def repI (mul : Nat → Nat → Nat) (cn : Nat → Bool) (one N c0 : Nat)
    (E Rp Cm : Nat → Nat) (r : Nat) : Bool :=
  strictB (Rp r) fun a => bAnd(Nat.blt a N, strictB (E a) fun x =>
    strictB (mul x x) fun x2 => strictB (mul x x2) fun y => bIf(Nat.beq y one,
      allN c0 (fun t => strictB (Cm (Nat.add (Nat.mul c0 r) t)) fun c => bAnd(Nat.blt c N,
        bAnd(bIf(Nat.beq t (nat_lit 0), true,
            Nat.blt (Cm (Nat.sub (Nat.add (Nat.mul c0 r) t) (nat_lit 1))) c),
          Nat.beq (mul (E c) x) (mul x (E c))))),
      bAnd(cn x2, cn y)))

end CFSG.KC.E27Orth

end
