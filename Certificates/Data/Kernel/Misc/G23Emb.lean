module

public import Certificates.Data.Kernel.Misc.G23

public section

namespace CFSG.KC.Misc.G23Emb

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24

@[expose] noncomputable def prodK (R js : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (oneF2 54) (fun j _ ih => mulF2 54 (nthV R j) ih) js

@[expose] noncomputable def c0K (U A2 : Nat) : Nat :=
  mulF2 54 U (mulF2 54 A2 (mulF2 54 (mulF2 54 U U) (mulF2 54 A2 A2)))

@[expose] noncomputable def embK (U V A1 A2 : Nat) : Bool :=
  letB (c0K U A2) fun C =>
  andB (Nat.beq (mulF2 54 A1 (mulF2 54 A1 A1)) (oneF2 54)) <|
  andB (Nat.beq (mulF2 54 A2 (mulF2 54 A2 A2)) (oneF2 54)) <|
  andB (Nat.beq (mulF2 54 U (mulF2 54 U U)) (oneF2 54)) <|
  andB (Nat.beq (mulF2 54 C (mulF2 54 C C)) (oneF2 54)) <|
  andB (Nat.beq (mulF2 54 C U) (mulF2 54 U C)) <|
  andB (Nat.beq (mulF2 54 C V) (mulF2 54 V C)) <|
  andB (Nat.beq (mulF2 54 C A1) (mulF2 54 A1 C)) <|
  andB (Nat.beq (mulF2 54 C A2) (mulF2 54 A2 C)) <|
  andB (Nat.beq (mulF2 54 A1 A2) (mulF2 54 A2 A1)) <|
  andB (Nat.beq (mulF2 54 V A2) (mulF2 54 A2 V)) <|
  andB (Nat.beq (mulF2 54 U A2) (mulF2 54 C (mulF2 54 A2 U))) <|
  andB (Nat.beq (mulF2 54 V A1) (mulF2 54 C (mulF2 54 C (mulF2 54 A1 V)))) <|
    Nat.beq (bit C 1) 1

end CFSG.KC.Misc.G23Emb

end
