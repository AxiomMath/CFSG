module

public import Certificates.Data.Kernel.GammaUViolK
public import CFSG.GF2Type.Smith1979.GammaU.Lagr

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C

open CFSG.GF2Type.Smith1979.GammaU in
@[expose] noncomputable def guOK (TH A : Nat) : Bool :=
  allBelow 12 (fun j => q0b (fld A j) == q0b (2 ^ j)) &&
    allBelow 12 (fun j => allBelow 12 fun k => f0b (fld A j) (fld A k) == f0b (2 ^ j) (2 ^ k)) &&
    (unitP TH A || antiP TH A)

@[expose] noncomputable def nmOK (L : List Nat) (A m m' : Nat) : Bool :=
  Nat.blt m' 32 && Nat.beq (mulP A (subQ L m)) (mulP (subQ L m') A)

@[expose] noncomputable def nlP (L : List Nat) (TH : Nat) (D0 SD : List Nat) (A : Nat)
    (nm : Nat → Nat) : Bool :=
  guOK TH A && Nat.beq (ap12 A 3072) 3072 && D0.all (fun d => memN (ap12 A d) SD) &&
    allBelow 32 fun m => nmOK L A m (nm m)

@[expose] noncomputable def cvAt (L : List Nat) (a b p₁ p₂ h : Nat) : Bool :=
  Nat.beq (mulP (subQ L a) h) (mulP h (subQ L p₁)) && Nat.beq (mulP (subQ L b) h) (mulP h (subQ L p₂))

@[expose] noncomputable def cvOK (L : List Nat) (NLG NLGI : Nat) (P : List Nat) (a b : Nat)
    (rec : List (List Nat)) : Bool :=
  Nat.blt (nthD 0 (nthD [] rec 0) 0) 2 && ltAll 6 (nthD [] rec 1) &&
    cvAt L a b (nthD 0 P (Nat.mul 2 (nthD 0 (nthD [] rec 0) 0)))
      (nthD 0 P (Nat.add (Nat.mul 2 (nthD 0 (nthD [] rec 0) 0)) 1)) (wordP NLG NLGI (nthD [] rec 1))

@[expose] noncomputable def rpAt (N2 : List Nat) (NN u : Nat) (rec : List (List Nat)) : Bool :=
  allBelow NN fun q => ltAll NN (nthD [] rec (Nat.add q 1)) &&
    Nat.beq (mulP u (nthD 0 N2 q)) (mulP (wordF (nthD 0 N2) (nthD [] rec (Nat.add q 1))) u)

@[expose] noncomputable def rpOK (N2 : List Nat) (NN : Nat) (RC RCI : List Nat) (F c : Nat)
    (rec : List (List Nat)) : Bool :=
  Nat.blt (nthD 0 (nthD [] rec 0) 0) (lenN RC) &&
    rpAt N2 NN (mulP (nthD 0 RCI (nthD 0 (nthD [] rec 0) 0)) (mulP F (nthD 0 RC c))) rec

end CFSG.KC.GUV

end
