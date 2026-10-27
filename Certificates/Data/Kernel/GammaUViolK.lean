module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C

@[expose] noncomputable def subQ (L : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => idP)
    (fun g _ ih m => mulP (ih (Nat.div m 2)) (bif Nat.beq (Nat.mod m 2) 1 then g else idP)) L m

@[expose] noncomputable def wordF (f : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun e _ ih => mulP (f e) ih) w

@[expose] noncomputable def ltAll (n : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Nat.blt e n && ih) w

@[expose] noncomputable def f2I3 (x y w : Nat) : Bool :=
  !(Nat.beq x 0) && !(Nat.beq y 0) && !(Nat.beq y x) && !(Nat.beq w 0) && !(Nat.beq w x) &&
    !(Nat.beq w y) && !(Nat.beq w (Nat.xor x y))

@[expose] noncomputable def antiP (TH A : Nat) : Bool :=
  Nat.beq (mulP A TH) (mulP TH (mulP TH A))

@[expose] noncomputable def unitP (TH A : Nat) : Bool := Nat.beq (mulP A TH) (mulP TH A)

@[expose] noncomputable def frOK (L : List Nat) (A u m : Nat) : Bool :=
  Nat.blt m 32 && Nat.beq (mulP A u) (mulP u (subQ L m))

@[expose] noncomputable def d2aAt (L : List Nat) (n m₁ m₂ m₃ : Nat) (w₁ w₂ w₃ : List Nat)
    (A u₁ u₂ u₃ : Nat) : Bool :=
  ltAll n w₁ && ltAll n w₂ && ltAll n w₃ && frOK L A u₁ m₁ && frOK L A u₂ m₂ && frOK L A u₃ m₃ &&
    f2I3 (ap12 u₁ 3072) (ap12 u₂ 3072) (ap12 u₃ 3072)

@[expose] noncomputable def d2aOK (L : List Nat) (TH : Nat) (f : Nat → Nat) (n : Nat)
    (rec : List (List Nat)) : Bool :=
  Nat.blt (nthD 0 (nthD [] rec 0) 0) 32 && antiP TH (subQ L (nthD 0 (nthD [] rec 0) 0)) &&
    d2aAt L n (nthD 0 (nthD [] rec 0) 1) (nthD 0 (nthD [] rec 0) 2) (nthD 0 (nthD [] rec 0) 3)
      (nthD [] rec 1) (nthD [] rec 2) (nthD [] rec 3) (subQ L (nthD 0 (nthD [] rec 0) 0))
      (wordF f (nthD [] rec 1)) (wordF f (nthD [] rec 2)) (wordF f (nthD [] rec 3))

@[expose] noncomputable def candL (CG FT FTi FC TH i X l : Nat) : Nat :=
  bif Nat.blt l 5 then look CG (Nat.add (Nat.mul 5 i) l)
  else bif Nat.blt l 10 then
    mulP (look FT X) (mulP (look CG (Nat.add (Nat.mul 5 (fld FC X)) (Nat.sub l 5))) (look FTi X))
  else TH

@[expose] noncomputable def letT (N2 : List Nat) (NN : Nat) (g : Nat → Nat) (C Ci e : Nat) : Nat :=
  bif Nat.blt e NN then nthD 0 N2 e else mulP C (mulP (g (Nat.sub e NN)) Ci)

@[expose] noncomputable def cjOK (L : List Nat) (S0 m C Ci : Nat) : Bool :=
  Nat.beq (mulP C Ci) idP && Nat.beq (mulP (subQ L m) C) (mulP C S0)

end CFSG.KC.GUV

end
