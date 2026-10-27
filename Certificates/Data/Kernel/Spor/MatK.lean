module

public import Certificates.Data.Kernel.MtxK

public section

namespace CFSG.KC.MatK

open CFSG.KC.Enum CFSG.KS CFSG.KC.Mtx

@[expose] noncomputable def hdrOK (h₀ h₁ h₂ h₃ k v : Nat) : Bool :=
  bAnd(Nat.blt k 4,
    Nat.beq v (nIf(Nat.beq k 0, h₀, nIf(Nat.beq k 1, h₁, nIf(Nat.beq k 2, h₂, h₃)))))

@[expose] noncomputable def matRun (h₀ h₁ h₂ h₃ cnt : Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun ph _ _ _ cc => bAnd(Nat.beq ph 1, Nat.beq cc cnt))
    (fun ch _ ih ph k v dg cc => strictB (Char.toNat ch) fun c =>
      bIf(Nat.beq ph 0,
        bIf(Nat.blt (CFSG.KC.SurjK.digV c) 10,
          strictB (Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV c)) (fun v' => ih 0 k v' 1 cc),
        bIf(Nat.beq c 10,
          bIf(Nat.beq dg 1,
            bAnd(hdrOK h₀ h₁ h₂ h₃ k v, bAnd(Nat.beq (Nat.succ k) 4, ih 1 0 0 0 0)),
            bAnd(Nat.beq k 4, ih 1 0 0 0 0)),
        bIf(wsB c,
          bIf(Nat.beq dg 1, bAnd(hdrOK h₀ h₁ h₂ h₃ k v, ih 0 (Nat.succ k) 0 0 0), ih 0 k 0 0 0),
          false))),
        bIf(wsB c, ih 1 0 0 0 cc,
          bIf(Nat.blt c 48, false, bIf(Nat.blt c 51,
            strictB (Nat.succ cc) (fun cc' => ih 1 0 0 0 cc'), false)))))
    cs

@[expose] noncomputable def matK (cs : List Char) (h₀ h₁ h₂ h₃ cnt : Nat) : Bool :=
  matRun h₀ h₁ h₂ h₃ cnt cs 0 0 0 0 0

end CFSG.KC.MatK

end
