module

public import Certificates.Data.Kernel.WittCnt

public section

namespace CFSG.KC.WCnt

open CFSG.KC.Enum

@[expose] noncomputable def fixCk (y k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => nIf(Nat.beq (pt y i) i, Nat.succ ih, ih)) k

@[expose] noncomputable def fixC (y : Nat) : Nat := fixCk y (nat_lit 22)

@[expose] noncomputable def fixL (l : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ ih => bAnd(Nat.beq (pt y i) i, ih)) l

@[expose] noncomputable def fourB (y : Nat) : Bool :=
  allB (fun i => Nat.beq (pt y (pt y (pt y (pt y i)))) i) (nat_lit 22)

@[expose] noncomputable def pwp (A B I : Nat) (w : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) I
    (fun b _ ih => strictN ih (fun g =>
      pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (nIf(b, B, A)) g)) w

end CFSG.KC.WCnt

end
