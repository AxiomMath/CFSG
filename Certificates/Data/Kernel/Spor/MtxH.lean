module

public import Certificates.Data.Kernel.MtxK

public section

namespace CFSG.KC.MtxH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Mtx

@[expose] noncomputable def tokHOK (w P h₀ h₁ h₂ h₃ k v : Nat) : Bool :=
  bIf(Nat.blt k 4,
    Nat.beq v (nIf(Nat.beq k 0, h₀, nIf(Nat.beq k 1, h₁, nIf(Nat.beq k 2, h₂, h₃)))),
    bAnd(Nat.ble 1 v, Nat.beq (pg w (mask w) P (Nat.sub k 4)) (Nat.sub v 1)))

@[expose] noncomputable def mtxHRun (n w P h₀ h₁ h₂ h₃ : Nat) (cs : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun k v dg => bIf(Nat.beq dg 1,
      bAnd(tokHOK w P h₀ h₁ h₂ h₃ k v, Nat.beq (Nat.succ k) (Nat.add n 4)),
      Nat.beq k (Nat.add n 4)))
    (fun ch _ ih k v dg => strictB (Char.toNat ch) fun c =>
      bIf(Nat.blt (CFSG.KC.SurjK.digV c) 10,
        ih k (Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV c)) 1,
      bIf(wsB c, bIf(Nat.beq dg 1, bAnd(tokHOK w P h₀ h₁ h₂ h₃ k v, ih (Nat.succ k) 0 0),
        ih k 0 0), false)))
    cs

@[expose] noncomputable def mtxHK (n w P h₀ h₁ h₂ h₃ : Nat) (cs : List Char) : Bool :=
  mtxHRun n w P h₀ h₁ h₂ h₃ cs 0 0 0

end CFSG.KC.MtxH

end
