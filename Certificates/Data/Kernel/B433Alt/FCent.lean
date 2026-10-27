module

public import Certificates.Data.Kernel.B433Alt.Fix

public section

namespace CFSG.KC.B4A

open CFSG.KC CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

@[expose] def fiveWL : List Nat := [1, 2, 0, 5]

@[expose] noncomputable def ptSet (pts : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) p)) pts

@[expose] noncomputable def sideAt (X b : Nat) : Nat :=
  sN X (fun X => Bool.rec (motive := fun _ => Nat) (Nat.xor allP X) X (bitB X b))

section
variable (Nf : Nat → Nat)

@[expose] noncomputable def fixW (w : List Nat) : Nat :=
  Nat.land (fixedSet (nat_lit 15) (apP Nf (nat_lit 15) w (idP (nat_lit 15)))) allP

@[expose] noncomputable def codeSet (F0 FS b : Nat) (taus : List (List Nat)) (pts : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Nat.land (sideAt FS b) (Nat.xor allP (ptSet pts)))
    (fun τ _ acc => sN acc (fun acc => Nat.land acc (sideAt (apP Nf (nat_lit 1) τ.reverse F0) b)))
    taus

end

end CFSG.KC.B4A

end
