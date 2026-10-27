module

public import Certificates.Data.Kernel.Misc.YamakiAut

public section

namespace CFSG.KD.SylowG2

open CFSG.KD.BfsK CFSG.KD.YamakiAut

@[expose] noncomputable def autAt3 (R RP : Nat → Nat) (o : Nat) (l0 l1 l2 : List Nat)
    (ONEP t : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (RP t) fun P =>
    Nat.beq (RP (recPOS R o 3 (Nat.add (Nat.mul t 3) 0))) (compL l0 P) &&
      Nat.beq (RP (recPOS R o 3 (Nat.add (Nat.mul t 3) 1))) (compL l1 P) &&
      Nat.beq (RP (recPOS R o 3 (Nat.add (Nat.mul t 3) 2))) (compL l2 P) &&
      (Nat.beq P ONEP == Nat.beq t 0)

@[expose] noncomputable def autChunk3 (R RP : Nat → Nat) (o : Nat) (l0 l1 l2 : List Nat)
    (ONEP n L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    cond (Nat.blt t n) (autAt3 R RP o l0 l1 l2 ONEP t) true

@[expose] noncomputable def invPos3 (R : Nat → Nat) (o n : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (v, j) :: ps => Nat.blt v n && Nat.beq (recPOS R o 3 (Nat.add (Nat.mul v 3) j)) 0 &&
      invPos3 R o n ps

end CFSG.KD.SylowG2

end
