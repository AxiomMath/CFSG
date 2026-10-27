module

public import Certificates.Data.Kernel.Spor.PEnum
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.PosWalk

open CFSG.KC.Loop CFSG.KS.PEnum

@[expose] noncomputable def wstepK (Cl : Nat → Nat) (k x l : Nat) : Nat :=
  r32 Cl (Nat.add (Nat.mul k x) l)

@[expose] noncomputable def walkK (Cl : Nat → Nat) (k : Nat) (wd : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (wstepK Cl k x l) ih) wd

@[expose] noncomputable def pathPosK (Cl : Nat → Nat) (k : Nat) (PL : Nat → Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun x _ => x)
    (fun _ ih x y => nIf(Nat.beq y (nat_lit 0), x,
      strictN (ih x (parOf PL y)) (fun p => wstepK Cl k p (labOf PL y)))) fuel

@[expose] noncomputable def cntK (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => nIf(f i, Nat.succ ih, ih)) n

end CFSG.KC.PosWalk

end
