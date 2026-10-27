module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.Misc.RuSq

open CFSG.KC.Enum CFSG.KS.Raw

@[expose] noncomputable def sqFixK (n w m : Nat) (TR : Nat → Nat) (o0 o1 a b x : Nat) : Bool :=
  strictB (TR (Nat.add o0 a)) fun T0 => strictB (TR (Nat.add o1 b)) fun T1 =>
    bAnd(Nat.blt x n, Nat.beq (pg w m T0 (pg w m T1 (pg w m T0 (pg w m T1 x)))) x)

@[expose] noncomputable def fix2K (n w m nw : Nat) (LR TR : Nat → Nat) (H : Nat) : Bool :=
  strictB (LR 0) fun R0 => strictB (LR 1) fun R1 => strictB (rcnt R1) fun c1 =>
  strictB (roff n nw R0) fun o0 => strictB (roff n nw R1) fun o1 =>
  allN (rcnt R0) fun a => allN c1 fun b =>
    sqFixK n w m TR o0 o1 a b (fld(H, Nat.mul w (Nat.add (Nat.mul a c1) b), m))

end CFSG.KC.Misc.RuSq

end
