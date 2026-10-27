module

public import Certificates.Data.Kernel.Misc.OmegaSixA

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def sKn (X w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun c ih => Nat.xor ih (Nat.mul (bitK w c) (subK X c))) n

@[expose] noncomputable def sK (X w : Nat) : Nat := sKn X w 6

@[expose] noncomputable def tiWitK (R : Nat → Nat) (X w : Nat) : Bool :=
  strictY (Nat.land w 32767) fun j => strictY (Nat.land (Nat.shiftRight w 15) 32767) fun k =>
  strictY (Nat.shiftRight w 30) fun c =>
  strictY (recX R 10 j) fun G => strictY (recX R 10 k) fun GI =>
  strictY (MULF (MULF G X) GI) fun U => strictY (MULF X U) fun P =>
    Nat.blt j 25920 && Nat.blt k 25920 && Nat.blt c 6 && Nat.beq (MULF G GI) ONE &&
      Nat.beq (MULF GI G) ONE && Nat.beq (MULF P P) ONE &&
      bIf(Nat.beq (sK X (subK U c)) 0, false, true)

@[expose] noncomputable def tiAt (R : Nat → Nat) (X w : Nat) : Bool :=
  bIf(Nat.beq (MULF X X) ONE, bIf(Nat.beq X ONE, true, bIf(rank1K X, true, tiWitK R X w)), true)

@[expose] noncomputable def tiChunk (R R' W : Nat → Nat) (L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t 51840, strictY (recX R' 3 t) fun X => tiAt R X (W t), true)

end CFSG.KD.OmegaSix

end
