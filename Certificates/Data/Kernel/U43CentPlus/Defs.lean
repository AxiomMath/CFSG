module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43CentPlus

open CFSG.KC.Enum

@[expose] noncomputable def bKey (f : Nat → Nat) : Nat :=
  Nat.lor (f (nat_lit 0)) (Nat.lor (Nat.shiftLeft (f (nat_lit 1)) (nat_lit 10))
    (Nat.shiftLeft (f (nat_lit 9)) (nat_lit 20)))

@[expose] noncomputable def incK (n : Nat) (K : Nat → Nat) : Bool :=
  allN (Nat.sub n (nat_lit 1)) (fun i => Nat.blt (K i) (K (Nat.succ i)))

@[expose] noncomputable def cntN (n : Nat) (p : Nat → Bool) : Nat :=
  foldN n (fun i s => nIf(p i, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def cDep (R : Nat → Nat) (r : Nat) : Nat := fld(R r, nat_lit 12, nat_lit 255)

@[expose] noncomputable def cRec (n w m : Nat) (Y R : Nat → Nat) (N k : Nat) (E EI : Nat → Nat)
    (g h r : Nat) : Bool :=
  strictB (R r) (fun d =>
  strictB fld(d, nat_lit 0, nat_lit 255) (fun par =>
  strictB fld(d, nat_lit 8, nat_lit 15) (fun lab =>
  strictB fld(d, nat_lit 12, nat_lit 255) (fun dep =>
    bIf(Nat.beq dep (nat_lit 0), eq2 n w m (Y r) g h,
      bAnd(Nat.blt par N, bAnd(Nat.blt lab k, bAnd(Nat.beq (cDep R par) (Nat.sub dep (nat_lit 1)),
        eq3 n w m (Y r) (E lab) (Y par) (EI lab)))))))))

@[expose] noncomputable def cTree (n w m : Nat) (Y R : Nat → Nat) (N k : Nat) (E EI : Nat → Nat)
    (g h : Nat) : Bool :=
  allN N (cRec n w m Y R N k E EI g h)

end CFSG.KC.U43CentPlus

end
