module

public import Certificates.Data.Kernel.Spor.F3Lane

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

@[expose] noncomputable def idUpTo (d : Nat) (I : V) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => bAnd(acc, bAnd(Nat.beq (blk d I i).p (Nat.shiftLeft (nat_lit 1) i),
      Nat.beq (blk d I i).m (nat_lit 0)))) n

@[expose] noncomputable def idOK (d : Nat) (I : V) : Bool := idUpTo d I d

end CFSG.KS.F3L

end
