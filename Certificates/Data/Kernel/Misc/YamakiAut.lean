module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KD.YamakiAut

open CFSG.KD.BfsK

@[expose] noncomputable def nib (c i : Nat) : Nat := Nat.mod (Nat.div c (Nat.pow 16 i)) 16

@[expose] noncomputable def compL (l : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ acc => Nat.add (nib a x) (Nat.mul 16 acc)) l

@[expose] noncomputable def autAt (R RP : Nat → Nat) (l0 l1 : List Nat) (ONEP t : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (RP t) fun P =>
    Nat.beq (RP (recPOS R 14 2 (Nat.add (Nat.mul t 2) 0))) (compL l0 P) &&
      Nat.beq (RP (recPOS R 14 2 (Nat.add (Nat.mul t 2) 1))) (compL l1 P) &&
      (Nat.beq P ONEP == Nat.beq t 0)

@[expose] noncomputable def autChunk (R RP : Nat → Nat) (l0 l1 : List Nat) (ONEP n L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n) (autAt R RP l0 l1 ONEP t) true

@[expose] noncomputable def invPosK (R : Nat → Nat) (n : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (v, j) :: ps => Nat.blt v n && Nat.beq (recPOS R 14 2 (Nat.add (Nat.mul v 2) j)) 0 &&
      invPosK R n ps

end CFSG.KD.YamakiAut

end
