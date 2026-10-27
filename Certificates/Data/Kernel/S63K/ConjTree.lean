module

public import Certificates.Data.Kernel.F2Word
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.S63K

open CFSG.KC.Enum

@[expose] noncomputable def cjStepK (G : Nat → Nat) (x l : Nat) : Nat :=
  CFSG.KC.F2W.mulW 24 (CFSG.KC.F2W.mulW 24 (G l) x) (G l)

@[expose] noncomputable def wordK (G : Nat → Nat) (I : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) I (fun k _ acc => CFSG.KC.F2W.mulW 24 (G k) acc) w

@[expose] noncomputable def treeAtK (F : Nat → Nat → Nat) (P Q : Nat → Nat) (ng i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true, strictB (Q i) fun q => strictB (Nat.div q ng) fun p =>
    bAnd(Nat.blt p i, Nat.beq (P i) (F (P p) (Nat.mod q ng))))

@[expose] noncomputable def distAtK (P S : Nat → Nat) (N k : Nat) : Bool :=
  bAnd(Nat.blt (S k) N, bAnd(Nat.blt (P k) (Nat.shiftLeft (nat_lit 1) (nat_lit 576)),
    bIf(Nat.beq (Nat.succ k) N, true, Nat.blt (P (S k)) (P (S (Nat.succ k))))))

@[expose] noncomputable def tagAtK (I : Nat) (A : Nat → Nat) (NA : Nat) (B : Nat → Nat) (NB x t : Nat) :
    Bool :=
  bIf(Nat.beq t (nat_lit 0),
    bIf(Nat.beq (Nat.mod (CFSG.KC.F2W.mulW 24 x x) (Nat.shiftLeft (nat_lit 1) (nat_lit 576))) I,
      Nat.beq x I, true),
    bIf(Nat.ble t NA, Nat.beq (A (Nat.sub t (nat_lit 1))) x,
      bAnd(Nat.blt (Nat.sub (Nat.sub t (nat_lit 1)) NA) NB,
        Nat.beq (B (Nat.sub (Nat.sub t (nat_lit 1)) NA)) x)))

end CFSG.KC.S63K

end
