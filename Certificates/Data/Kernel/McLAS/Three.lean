module

public import Certificates.Data.Kernel.McLAS.Pair

public section

namespace CFSG.KS.McLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def ord6K (x : Nat) : Bool :=
  strictB (pcK x x) fun x2 => strictB (pcK x2 x2) fun x4 =>
    bIf(Nat.beq x4 idK, true, strictB (pcK x2 x) fun x3 =>
      bIf(Nat.beq (pcK x3 x3) idK, true, Nat.beq (pcK x4 x) idK))

@[expose] noncomputable def ord3K (x : Nat) : Bool :=
  bAnd(Nat.beq (pwK (nat_lit 3) x) idK, bIf(Nat.beq (pwK (nat_lit 1) x) idK, false, true))

@[expose] noncomputable def commK (x y : Nat) : Bool := Nat.beq (pcK x y) (pcK y x)

@[expose] noncomputable def inRowK (S : Nat → Nat) (c i : Nat) : Bool :=
  bIf(allN c fun j => bIf(Nat.beq (r32 S j) i, false, true), false, true)

end CFSG.KS.McLAS

end
