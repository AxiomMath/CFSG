module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.Bytes

@[expose] noncomputable def run (F : Nat → Nat) (lb len : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i len)
    (fun ch _ ih i => (fun c => bAnd(Nat.blt c (nat_lit 128), bAnd(Nat.blt i len,
        bAnd(Nat.beq c (fld(F (Nat.div i lb), Nat.mul (nat_lit 8) (Nat.mod i lb), nat_lit 255)),
          ih (Nat.succ i)))))
      (Char.toNat ch))
    cs

@[expose] noncomputable def bytesEqK (cs : List Char) (F : Nat → Nat) (lb len : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) lb, run F lb len cs (nat_lit 0))

end CFSG.KS.Bytes

end
