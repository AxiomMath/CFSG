module

public import CFSG.Certificates.Kernel.Th.S.BigS

public section

namespace CFSG.KC.ThRk10508

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def comB (c rm P Q : Nat) : Bool :=
  Nat.beq (mulB c rm P Q) (mulB c rm Q P)

@[expose] noncomputable def eqBB (a b : Bool) : Bool := Bool.rec (notB b) b a

@[expose] noncomputable def memL (Ls : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ acc => Bool.rec acc true (Nat.beq a k)) Ls

@[expose] noncomputable def getL (Ls : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun D _ acc j => Nat.rec (motive := fun _ => List Nat) D (fun j' _ => acc j') j) Ls

@[expose] noncomputable def getN (Ns : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ acc j => Nat.rec (motive := fun _ => Nat) a (fun j' _ => acc j') j) Ns

@[expose] noncomputable def allN (f : Nat → Bool) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => andB (f (Nat.add lo j)) acc) n

@[expose] noncomputable def allL (f : Nat → Bool) (Ls : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ acc => andB (f a) acc) Ls

variable (RB : Nat → Nat) (c rm ONE : Nat)

@[expose] noncomputable def cqK (Cl : List Nat) (k : Nat) : Bool :=
  eqBB (comB c rm (RB (25 + k)) (RB 13)) (memL Cl k)

@[expose] noncomputable def cqChunk (Cl : List Nat) (g : Nat) : Bool :=
  allN (cqK RB c rm Cl) (Nat.mul 64 g) 64

@[expose] noncomputable def ccK (Cl : List Nat) (k : Nat) : Bool :=
  allL (fun l => comB c rm (RB (25 + k)) (RB (25 + l))) Cl

@[expose] noncomputable def rowI (L : Nat → Nat) (Ks Es Ws Cl : List Nat) (Ds : List (List Nat))
    (Ts : List Nat) (i : Nat) : Bool :=
  andB (Nat.beq (L i) (mulB c rm (RB (25 + getN Ks i))
      (wordAB c rm ONE (RB 13) (RB 14) (RB 15) (getN Es i) (getN Ws i))))
    (andB (comB c rm (L i) (RB 13))
      (andB (allL (fun k => eqBB (comB c rm (RB (25 + k)) (L i)) (memL (getL Ds i) k)) Cl)
        (Bool.rec
          (allL (fun k => notB (Nat.beq (powB c rm ONE (mulB c rm (RB (25 + k)) (L i)) 2 2) ONE)) Cl)
          true (memL Ts i))))

end CFSG.KC.ThRk10508

end
