module

public import Certificates.Data.Kernel.G2Three.Defs
public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.Misc.G23F3

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KC.Misc.G24 CFSG.KD.G2Three

@[expose] noncomputable def constsK : Bool := consts3OK 14 5 196 LO RM CI ONE UP

@[expose] noncomputable def bitsK (v : Nat) (m : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => Nat.add (Nat.mul 2 ih) (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq e v))) m

@[expose] noncomputable def pkK (m : List Nat) : Nat :=
  Nat.add (Nat.mul (Nat.shiftLeft 1 196) (bitsK 2 m)) (bitsK 1 m)

@[expose] noncomputable def wordK (R js : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun j _ ih => MUL (nthV R j) ih) js

@[expose] noncomputable def two (X t : Nat) : Bool :=
  andB (Nat.beq (bit X t) 0) (Nat.beq (bit X (Nat.add 196 t)) 1)

@[expose] noncomputable def splitK (U V Z A1 A2 C : Nat) : Bool :=
  andB (Nat.beq (MUL A1 (MUL A1 A1)) ONE) <| andB (Nat.beq (MUL A2 (MUL A2 A2)) ONE) <|
  andB (Nat.beq (MUL Z (MUL Z Z)) ONE) <| andB (Nat.beq (MUL U (MUL U U)) ONE) <|
  andB (Nat.beq (MUL A1 A2) (MUL A2 A1)) <|
  andB (Nat.beq (MUL U A1) (MUL A1 U)) <| andB (Nat.beq (MUL U A2) (MUL A2 U)) <|
  andB (Nat.beq (MUL V A1) (MUL A1 V)) <| andB (Nat.beq (MUL V A2) (MUL A2 V)) <|
  andB (Nat.beq (MUL Z A1) (MUL A1 Z)) <| andB (Nat.beq (MUL Z A2) (MUL A2 Z)) <|
  andB (Nat.beq (MUL U Z) (MUL Z U)) <| andB (Nat.beq (MUL V Z) (MUL Z V)) <|
  andB (Nat.beq (MUL U V) (MUL Z (MUL V U))) <|
  andB (Nat.beq (MUL C A1) (MUL A2 C)) <| andB (Nat.beq (MUL C A2) (MUL A1 (MUL A2 C))) <|
  andB (two A1 5) (two Z 12)

@[expose] noncomputable def liftK (R : List Nat) (eqs : List (List Nat × List Nat))
    (nes : List (List Nat)) : Bool :=
  andB (List.rec (motive := fun _ => Bool) true
      (fun p _ ih => andB (Nat.beq (wordK R p.1) (wordK R p.2)) ih) eqs)
    (List.rec (motive := fun _ => Bool) true
      (fun w _ ih => andB (notB (Nat.beq (wordK R w) ONE)) ih) nes)

end CFSG.KC.Misc.G23F3

end
