module

public import Certificates.Data.Kernel.U43Mod.InvDefs

public section

namespace CFSG.KC.U43Out

open CFSG.KC.Enum CFSG.KC.U43Inv

@[expose] noncomputable def f4 (r : Nat) : Nat := fld(r, nat_lit 53, nat_lit 1023)

@[expose] noncomputable def k4Rec (R : Nat → Nat) (Gk : Nat → Nat → Nat) (k : Nat) : Bool :=
  strictB (R k) fun r => bIf(Nat.beq k (nat_lit 0), Nat.beq (f4 r) (nat_lit 84),
    Nat.beq (f4 r) (Gk (klab r) (f4 (R (kpar r)))))

@[expose] noncomputable def k4Tree (R : Nat → Nat) (n : Nat) (Gk : Nat → Nat → Nat) : Bool :=
  allN n (k4Rec R Gk)

@[expose] noncomputable def tClos (R : Nat → Nat) (n nl : Nat) (Gk : Nat → Nat → Nat)
    (tbl : List Nat) : Bool :=
  lwalk (fun i x => bAnd(Nat.blt x n, bAnd(keys3 (Gk (Nat.mod i nl)) (R (Nat.div i nl)) (R x),
    Nat.beq (f4 (R x)) (Gk (Nat.mod i nl) (f4 (R (Nat.div i nl)))))))
    (Nat.mul n nl) tbl (nat_lit 0)

@[expose] noncomputable def pwv (Lp : Nat → Nat → Nat) (W len q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => ih (Lp fld(W, Nat.shiftLeft k (nat_lit 1), nat_lit 3) q)) len q

@[expose] noncomputable def orbOK (f : Nat → Nat) (q : Nat) (n p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih p => strictB (f p) fun p' => bAnd(bNot (Nat.beq p' q), ih p')) n p

end CFSG.KC.U43Out

end
