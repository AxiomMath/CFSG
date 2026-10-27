module

public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def rowBitK (n : Nat) (B : Nat → Nat) : Bool :=
  allN n fun p => Nat.ble (r32 B p) (nat_lit 1)

@[expose] noncomputable def blockK (n w : Nat) (B : Nat → Nat) (G s : Nat) : Bool :=
  allN n fun p => Nat.beq (r32 B (pg w (mask w) G p)) (Nat.xor (r32 B p) s)

@[expose] noncomputable def notPowK (n w m c x : Nat) : Bool :=
  allN m fun k => bIf(Nat.beq c (pw n w x (Nat.succ k)), false, true)

@[expose] noncomputable def movesK (n w m g gi x : Nat) : Bool :=
  notPowK n w m (pcomp n w (mask w) (pcomp n w (mask w) g x) gi) x

end CFSG.KS.MaxD2
