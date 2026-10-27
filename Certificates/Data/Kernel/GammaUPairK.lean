module

public import Certificates.Data.Kernel.GammaUViolK

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C

@[expose] noncomputable def letP (g₁ g₂ : Nat → Nat) (C₁ C₁i C₂ C₂i TH e : Nat) : Nat :=
  bif Nat.blt e 11 then mulP C₁ (mulP (g₁ e) C₁i)
  else bif Nat.blt e 22 then mulP C₂ (mulP (g₂ (Nat.sub e 11)) C₂i)
  else bif Nat.beq e 22 then mulP C₁ (mulP (mulP TH TH) C₁i)
  else mulP C₂ (mulP (mulP TH TH) C₂i)

@[expose] noncomputable def d1Cmp (L : List Nat) (h hA : Nat) : Bool :=
  allBelow 32 fun m' => !(Nat.beq hA (mulP (subQ L m') h))

@[expose] noncomputable def d1At (L : List Nat) (m h : Nat) : Bool :=
  Nat.blt m 32 && Nat.beq (ap12 h 3072) 3072 && d1Cmp L h (mulP h (subQ L m))

@[expose] noncomputable def d1OK (L : List Nat) (f : Nat → Nat) (n : Nat) (rec : List (List Nat)) :
    Bool :=
  ltAll n (nthD [] rec 1) && d1At L (nthD 0 (nthD [] rec 0) 0) (wordF f (nthD [] rec 1))

@[expose] noncomputable def resFwd (N2 : List Nat) (NN : Nat) (f : Nat → Nat) (n U : Nat)
    (rec : List (List Nat)) : Bool :=
  allBelow n fun e => ltAll NN (nthD [] rec (Nat.add e 1)) &&
    Nat.beq (mulP (f e) U) (mulP U (wordF (nthD 0 N2) (nthD [] rec (Nat.add e 1))))

@[expose] noncomputable def resBwd (N2 : List Nat) (NN : Nat) (f : Nat → Nat) (n U : Nat)
    (rec : List (List Nat)) : Bool :=
  allBelow NN fun q => ltAll n (nthD [] rec (Nat.add (Nat.add n 1) q)) &&
    Nat.beq (mulP U (nthD 0 N2 q)) (mulP (wordF f (nthD [] rec (Nat.add (Nat.add n 1) q))) U)

@[expose] noncomputable def resAt (N2 : List Nat) (NN : Nat) (f : Nat → Nat) (n U Ui : Nat)
    (rec : List (List Nat)) : Bool :=
  Nat.beq (mulP U Ui) idP && resFwd N2 NN f n U rec && resBwd N2 NN f n U rec

@[expose] noncomputable def resOK (N2 : List Nat) (NN : Nat) (f : Nat → Nat) (n : Nat)
    (RC RCI : List Nat) (rec : List (List Nat)) : Bool :=
  Nat.blt (nthD 0 (nthD [] rec 0) 0) (lenN RC) &&
    resAt N2 NN f n (nthD 0 RC (nthD 0 (nthD [] rec 0) 0)) (nthD 0 RCI (nthD 0 (nthD [] rec 0) 0))
      rec

@[expose] noncomputable def pairW (L : List Nat) (TH : Nat) (N2 : List Nat) (NN : Nat)
    (f : Nat → Nat) (RC RCI : List Nat) (tg : Nat) (rec : List (List Nat)) : Bool :=
  bif Nat.beq tg 0 then d2aOK L TH f 24 rec
  else bif Nat.beq tg 1 then d1OK L f 24 rec
  else Nat.beq tg 2 && resOK N2 NN f 24 RC RCI rec

@[expose] noncomputable def dupOK (g g' : Nat → Nat) (ws : List (List Nat)) : Bool :=
  allBelow 5 fun l => ltAll 11 (nthD [] ws l) &&
    Nat.beq (wordF g (nthD [] ws l)) (g' (Nat.add 5 l))

end CFSG.KC.GUV

end
