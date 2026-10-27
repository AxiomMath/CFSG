module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.SporSch.LyMat

public section

namespace CFSG.KD.U43Pk

open CFSG.KC.Enum

@[expose] def MT : Nat :=
  5107958271419843920193557880922165469200445146711473720438786334434434179969678641066430418649088

@[expose] def AT : Nat :=
  8986690708024339884259668388453865091868182506470258411551265922896781674643265104972283578167824

@[expose] def BT : Nat := 32317452576

@[expose] def MCT : Nat := 26408595744

@[expose] def IDK : Nat := 3458767812358569987

@[expose] noncomputable def dg (P j : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.shiftLeft j 2)) 15

@[expose] noncomputable def mT (c d : Nat) : Nat := dg MT (Nat.add (Nat.mul 9 c) d)

@[expose] noncomputable def aT (c d : Nat) : Nat := dg AT (Nat.add (Nat.mul 9 c) d)

@[expose] noncomputable def packK (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => strictN acc fun a => Nat.add a (Nat.shiftLeft (f k) (Nat.shiftLeft k 2))) 16

@[expose] noncomputable def mapK (B P : Nat) : Nat := packK fun k => dg B (dg P k)

@[expose] noncomputable def entK (G Y i j : Nat) : Nat :=
  aT (aT (aT (mT (dg G (Nat.mul 4 i)) (dg Y j))
    (mT (dg G (Nat.add (Nat.mul 4 i) 1)) (dg Y (Nat.add 4 j))))
    (mT (dg G (Nat.add (Nat.mul 4 i) 2)) (dg Y (Nat.add 8 j))))
    (mT (dg G (Nat.add (Nat.mul 4 i) 3)) (dg Y (Nat.add 12 j)))

@[expose] noncomputable def matK (G Y : Nat) : Nat :=
  packK fun k => entK G Y (Nat.div k 4) (Nat.mod k 4)

@[expose] noncomputable def mulK (G P : Nat) : Nat :=
  strictN (Bool.rec (motive := fun _ => Nat) P (mapK BT P) (Nat.beq (dg G 16) 1)) fun Y =>
    Nat.add (matK G Y) (Nat.shiftLeft (Nat.mod (Nat.add (dg G 16) (dg P 16)) 2) 64)

@[expose] noncomputable def fnzK (R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => strictN (dg R (Nat.sub 15 k)) fun v => Bool.rec (motive := fun _ => Nat) v acc
      (Nat.beq v 0)) 16

@[expose] noncomputable def nrmK (R : Nat) : Nat :=
  strictN (dg MCT (fnzK R)) fun c =>
    Nat.add (mapK (Nat.shiftRight MT (Nat.shiftLeft (Nat.mul 9 c) 2)) R) (Nat.shiftLeft (dg R 16) 64)

@[expose] noncomputable def actK (G P : Nat) : Nat := strictN (mulK G P) nrmK

@[expose] noncomputable def conjTK (P : Nat) : Nat :=
  packK fun k => dg BT (dg P (Nat.add (Nat.mul 4 (Nat.mod k 4)) (Nat.div k 4)))

@[expose] noncomputable def rawValidK (P : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight P 68) 0, bAnd(allBlk 0 (fun j => Nat.blt (dg P j) 9) 16,
    bAnd(Nat.blt (dg P 16) 2, Nat.beq (matK (conjTK P) P) IDK)))

@[expose] noncomputable def validK (P : Nat) : Bool := bAnd(rawValidK P, Nat.beq (nrmK P) P)

@[expose] noncomputable def posK (n : Nat) (PA LA : Nat → Nat) (j : Nat) : Nat :=
  Nat.add (Nat.mul n (PA j)) (LA j)

@[expose] noncomputable def ptK (n N : Nat) (G T : Nat → Nat) (E : Nat → Nat → Nat)
    (PA LA SO SOI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun P =>
  bAnd(validK P, bAnd(CFSG.KS.SporSch.LyM.sortB T SO SOI N i,
    bAnd(allBlk 0 (fun k => strictB (E i k) fun e =>
      bAnd(Nat.blt e N, bAnd(Nat.beq (actK (G k) P) (T e),
        bIf(Nat.beq e 0, true, Nat.ble (posK n PA LA e) (Nat.add (Nat.mul n i) k))))) n,
    bIf(Nat.beq i 0, bAnd(Nat.beq P IDK, bAnd(Nat.beq (PA 0) 0, Nat.beq (LA 0) 0)),
      bAnd(Nat.blt (PA i) i, bAnd(Nat.blt (LA i) n, bAnd(Nat.beq (E (PA i) (LA i)) i,
        bIf(Nat.beq (Nat.succ i) N, true,
          Nat.blt (posK n PA LA i) (posK n PA LA (Nat.succ i))))))))))

@[expose] noncomputable def blkK (n N : Nat) (G T : Nat → Nat) (E : Nat → Nat → Nat)
    (PA LA SO SOI : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i fun i => ptK n N G T E PA LA SO SOI i) len

end CFSG.KD.U43Pk

end
