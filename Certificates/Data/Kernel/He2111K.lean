module

public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Misc.HexFlat

public section

namespace CFSG.KC.He2111

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def e14 (P x : Nat) : Nat := pg (nat_lit 14) (nat_lit 16383) P x

@[expose] noncomputable def brK (P G0 G1 : Nat) (PI AL BE : Nat → Nat) (x : Nat) : Bool :=
  strictB (e14 P x) fun y => strictB (e14 G0 x) fun u => strictB (e14 G1 x) fun v =>
    bAnd(Nat.blt y (nat_lit 8330), bAnd(Nat.blt u (nat_lit 8330), bAnd(Nat.blt v (nat_lit 8330),
    bAnd(Nat.beq (r32 PI y) x, bAnd(Nat.beq (r32 AL y) (e14 P u), Nat.beq (r32 BE y) (e14 P v))))))

@[expose] noncomputable def brSl (P G0 G1 : Nat) (PI AL BE : Nat → Nat) (lo len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add lo d) fun x =>
    bIf(Nat.blt x (nat_lit 8330), brK P G0 G1 PI AL BE x, true)

end CFSG.KC.He2111

end
