module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.SetWalk

open CFSG.KC.Enum

@[expose] noncomputable def rd (T : Nat → Nat) (i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 8)) fun b =>
    fld(T b, Nat.mul (nat_lit 80) (Nat.land i (nat_lit 255)), nat_lit 1208925819614629174706175)

@[expose] noncomputable def keyR (T : Nat → Nat) (i : Nat) : Nat :=
  Nat.shiftRight (rd T i) (nat_lit 16)

@[expose] noncomputable def keyH (k w m wr mr R S : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun lo => nIf(Nat.blt lo k, fld(R, Nat.mul wr fld(S, Nat.mul w lo, m), mr), nat_lit 0))
    (fun d ih lo => Nat.add (ih lo) (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def keyS (k w m wr mr R d S : Nat) : Nat := keyH k w m wr mr R S d (nat_lit 0)

@[expose] noncomputable def cstep (k w m NC : Nat) (T CS CP : Nat → Nat) (go : Nat → Nat → Nat)
    (has G S j : Nat) : Nat :=
  strictN j fun j =>
  nIf(Nat.beq has (nat_lit 0), j,
    nIf(Nat.beq j (nat_lit 0), nat_lit 0,
      strictN (pcomp k w m G S) fun S' => strictN (rd T j) fun rc =>
        nIf(Nat.beq (Nat.land (Nat.shiftRight rc (nat_lit 2)) (nat_lit 1)) (nat_lit 0), go j S',
          strictN (Nat.land (Nat.shiftRight rc (nat_lit 3)) (nat_lit 127)) fun c =>
            strictN (CP c) fun cp =>
              nIf(bAnd(Nat.blt c NC, bAnd(Nat.beq (Nat.land cp (nat_lit 1048575)) j,
                  bAnd(Nat.blt j (Nat.shiftRight cp (nat_lit 20)), Nat.beq (CS c) S'))),
                Nat.shiftRight cp (nat_lit 20), nat_lit 0))))

@[expose] noncomputable def walk (k w m wr mr R d NC G0 G1 : Nat) (T CS CP : Nat → Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih i S => strictN (rd T i) fun r =>
      nIf(Nat.beq (keyS k w m wr mr R d S) (Nat.shiftRight r (nat_lit 16)),
        cstep k w m NC T CS CP ih (Nat.land (Nat.shiftRight r (nat_lit 1)) (nat_lit 1)) G1 S
          (cstep k w m NC T CS CP ih (Nat.land r (nat_lit 1)) G0 S (Nat.succ i)),
        nat_lit 0))

@[expose] noncomputable def chunkOK (k w m wr mr R d NC G0 G1 N D : Nat) (T CS CP : Nat → Nat)
    (c : Nat) : Bool :=
  strictB (CP c) fun cp => strictB (Nat.land cp (nat_lit 1048575)) fun p =>
    strictB (CS c) fun S =>
    bAnd(Nat.blt c NC, bAnd(Nat.blt p N,
      bAnd(Nat.beq (Nat.land (rd T p) (nat_lit 1020)) (Nat.add (nat_lit 4) (Nat.shiftLeft c (nat_lit 3))),
        Nat.beq (walk k w m wr mr R d NC G0 G1 T CS CP D p S) (Nat.shiftRight cp (nat_lit 20)))))

@[expose] noncomputable def skAt (SKT : Nat → Nat) (j : Nat) : Nat :=
  strictN (Nat.shiftRight j (nat_lit 8)) fun b =>
    fld(SKT b, Nat.mul (nat_lit 16) (Nat.land j (nat_lit 255)), nat_lit 65535)

@[expose] noncomputable def sortOK (T SKT : Nat → Nat) (N lo len : Nat) : Bool :=
  allN len fun t => strictB (Nat.add lo t) fun j =>
    strictB (skAt SKT j) fun a => strictB (skAt SKT (Nat.succ j)) fun b =>
      bAnd(Nat.blt a N, bAnd(Nat.blt b N, Nat.blt (keyR T a) (keyR T b)))

@[expose] noncomputable def setMask (k w m S : Nat) : Nat :=
  foldN k (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) fld(S, Nat.mul w i, m))) (nat_lit 0)

@[expose] noncomputable def listK (w m : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun S => Nat.beq S (nat_lit 0))
    (fun a _ ih S => bAnd(Nat.beq (Nat.land S m) a, ih (Nat.shiftRight S w)))

@[expose] noncomputable def fixOK (k w m G S : Nat) : Bool :=
  strictB (setMask k w m S) fun M =>
    allN k fun i =>
      Nat.beq (Nat.land (Nat.shiftRight M (pg w m G fld(S, Nat.mul w i, m))) (nat_lit 1)) (nat_lit 1)

end CFSG.KC.SetWalk

end
