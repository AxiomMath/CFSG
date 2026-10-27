module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.PairCount

open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def cntAt (N w K1 K2 i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Nat.add (Nat.add acc
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (pg w (mask w) K1 x) i)))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (pg w (mask w) K2 x) i)))
    N

@[expose] noncomputable def cntK (N w K1 K2 lo cnt c : Nat) : Bool :=
  allN cnt fun t => Nat.beq (cntAt N w K1 K2 (Nat.add lo t)) c

@[expose] noncomputable def pairK (N w K1 K2 : Nat) : Bool :=
  allN N fun x => Nat.blt (pg w (mask w) K1 x) (pg w (mask w) K2 x)

end CFSG.KC.Misc.PairCount

end
