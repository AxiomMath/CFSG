module

public import Certificates.Data.Kernel.LyDce.Cover

public section

namespace CFSG.KC.LyModel

open CFSG.KC CFSG.KC.Loop CFSG.KC.LyDce CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def allFrom (lo n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f (Nat.add lo i)) ih) n

@[expose] noncomputable def memN (p : Nat) (R : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (Nat.beq a p) ih) R

@[expose] noncomputable def invAt (Tc Td root C : Nat) (ys : List Nat) (l : Nat) : Bool :=
  orB (notB (Nat.blt l nL)) (orB (Nat.beq l root)
    (orB (Nat.beq (Nat.land (Nat.shiftRight C l) 1) 1) (notB (Nat.beq (mvC Tc Td ys l) l))))

@[expose] noncomputable def orbOK (Tc Td : Nat) (us : List (List Nat))
    (es : List (Nat × Nat × Nat)) (R : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun e _ ih R => andB (andB (memN e.2.1 R) (andB (Nat.blt e.2.2 4)
      (Nat.beq (mvC Tc Td (us.getD e.2.2 []) e.2.1) e.1))) (ih (e.1 :: R))) es R

@[expose] noncomputable def movedM (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun u acc => strictN acc fun a =>
    Nat.lor a (Nat.xor (netApply 17 (Nat.shiftLeft 1 17) 1 N (idPlane (Nat.shiftLeft 1 17) u))
      (idPlane (Nat.shiftLeft 1 17) u))) 17

@[expose] noncomputable def fixM (N M : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.xor (movedM N) (ones 131072)) (ones 66825)) M

end CFSG.KC.LyModel

end
