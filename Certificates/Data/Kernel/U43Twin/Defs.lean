module

public import Certificates.Data.Kernel.U43Pk.Defs

public section

namespace CFSG.KD.U43Twin

open CFSG.KC.Enum CFSG.KD.U43Pk

@[expose] noncomputable def cjK (G H P : Nat) : Nat :=
  strictN (mulK G P) fun Y => strictN (mulK Y H) nrmK

@[expose] noncomputable def ptAK (n N : Nat) (A : Nat → Nat → Nat) (R : Nat) (T : Nat → Nat)
    (E : Nat → Nat → Nat) (PA LA SO SOI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun P =>
  bAnd(validK P, bAnd(CFSG.KS.SporSch.LyM.sortB T SO SOI N i,
    bAnd(allBlk 0 (fun k => strictB (E i k) fun e =>
      bAnd(Nat.blt e N, bAnd(Nat.beq (A k P) (T e),
        bIf(Nat.beq e 0, true, Nat.ble (posK n PA LA e) (Nat.add (Nat.mul n i) k))))) n,
    bIf(Nat.beq i 0, bAnd(Nat.beq P R, bAnd(Nat.beq (PA 0) 0, Nat.beq (LA 0) 0)),
      bAnd(Nat.blt (PA i) i, bAnd(Nat.blt (LA i) n, bAnd(Nat.beq (E (PA i) (LA i)) i,
        bIf(Nat.beq (Nat.succ i) N, true,
          Nat.blt (posK n PA LA i) (posK n PA LA (Nat.succ i))))))))))

@[expose] noncomputable def blkAK (n N : Nat) (A : Nat → Nat → Nat) (R : Nat) (T : Nat → Nat)
    (E : Nat → Nat → Nat) (PA LA SO SOI : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i fun i => ptAK n N A R T E PA LA SO SOI i) len

end CFSG.KD.U43Twin

end
