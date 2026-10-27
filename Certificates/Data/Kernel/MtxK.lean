module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.SurjK

public section

namespace CFSG.KC.Mtx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def wsB (c : Nat) : Bool :=
  bIf(Nat.beq c 32, true, bIf(Nat.beq c 10, true, bIf(Nat.beq c 9, true, Nat.beq c 13)))

@[expose] noncomputable def tokOK (w P k v : Nat) : Bool :=
  bIf(Nat.blt k 4, true, bAnd(Nat.ble 1 v, Nat.beq (pg w (mask w) P (Nat.sub k 4)) (Nat.sub v 1)))

@[expose] noncomputable def mtxRun (n w P : Nat) (cs : List Char) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun k v dg => bIf(Nat.beq dg 1, bAnd(tokOK w P k v, Nat.beq (Nat.succ k) (Nat.add n 4)),
      Nat.beq k (Nat.add n 4)))
    (fun ch _ ih k v dg => strictB (Char.toNat ch) fun c =>
      bIf(Nat.blt (CFSG.KC.SurjK.digV c) 10,
        ih k (Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV c)) 1,
      bIf(wsB c, bIf(Nat.beq dg 1, bAnd(tokOK w P k v, ih (Nat.succ k) 0 0), ih k 0 0), false)))
    cs

@[expose] noncomputable def mtxK (n w P : Nat) (cs : List Char) : Bool := mtxRun n w P cs 0 0 0

end CFSG.KC.Mtx

end
