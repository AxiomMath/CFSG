module

public import Certificates.Data.Kernel.CosetLat.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.A8Part

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def bitN (S i : Nat) : Nat := Nat.land (Nat.shiftRight S i) (nat_lit 1)

@[expose] noncomputable def psAt (S c : Nat) : Bool :=
  orB (allN (nat_lit 8) fun i =>
      Nat.beq (bitN S (CFSG.KC.Enum.pg (nat_lit 4) (CFSG.KS.mask (nat_lit 4)) c i)) (bitN S i))
    (allN (nat_lit 8) fun i => notB
      (Nat.beq (bitN S (CFSG.KC.Enum.pg (nat_lit 4) (CFSG.KS.mask (nat_lit 4)) c i)) (bitN S i)))

@[expose] noncomputable def trans3At (M : Nat → Nat → Nat) (ES : Nat → Nat) (nS : Nat)
    (RC : Nat → Nat) (nR : Nat) (EH : Nat → Nat) (nH : Nat) (EU UR : Nat → Nat) (i : Nat) :
    Bool :=
  letB (UR i) fun r => letB (Nat.land r (nat_lit 255)) fun s =>
    letB (Nat.land (Nat.shiftRight r (nat_lit 8)) (nat_lit 255)) fun j =>
    letB (Nat.shiftRight r (nat_lit 16)) fun y =>
      andB (Nat.blt s nS) (andB (Nat.blt j nR) (andB (Nat.blt y nH)
        (Nat.beq (M (ES s) (EU i)) (M (RC j) (EH y)))))

@[expose] noncomputable def cosAt (M : Nat → Nat → Nat) (TE TP : Nat → Nat) (nP X : Nat)
    (CS : Nat → Nat) (k : Nat) : Bool :=
  letB (CS k) fun r => letB (Nat.land r (nat_lit 255)) fun m =>
    andB (Nat.blt m nP) (Nat.beq (TE k)
      (Bool.rec (motive := fun _ => Nat) (M (TP m) X) (TP m)
        (Nat.beq (Nat.shiftRight r (nat_lit 8)) (nat_lit 0))))

end CFSG.KC.A8Part

end
