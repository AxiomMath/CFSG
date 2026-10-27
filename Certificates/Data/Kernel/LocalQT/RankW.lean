module

public import Certificates.Data.Kernel.LocalQT.BaseW

public section

namespace CFSG.KC.LQT.RW

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW

@[expose] noncomputable def findW (g : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) g 0

@[expose] noncomputable def genIdxW (W g gg PK CK i : Nat) : Nat :=
  findW g fun j => Nat.beq (imgW W CK (Nat.add (Nat.mul (imgW W PK i) gg) j)) i

@[expose] noncomputable def mulIdxW (W g gg PK CK f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ k => k)
    (fun _ ih i k => Bool.rec (motive := fun _ => Nat)
      (imgW W CK (Nat.add (Nat.mul (ih (imgW W PK i) k) gg) (genIdxW W g gg PK CK i))) k
      (Nat.beq i 0)) f

@[expose] noncomputable def hasW (l : List Nat) (x : Nat) : Bool := anyL l (Nat.beq x)

@[expose] noncomputable def mapW (f : Nat → Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.cons (f x) ih) l

@[expose] noncomputable def dfsW (mul : Nat → Nat → Nat) (invs : List Nat) (d : Nat) :
    List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → List Nat → Bool) (fun _ _ => true)
    (fun _ ih L S => anyL invs fun c => andB (andB (notB (hasW S c))
      (allL L fun l => Nat.beq (mul c l) (mul l c)))
      (ih (List.cons c L) (appK S (mapW (mul c) S)))) d

@[expose] noncomputable def filterN (N : Nat) (f : Nat → Bool) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ i))
      (List.cons i (ih (Nat.succ i))) (f i)) N 0

end CFSG.KC.LQT.RW

end
