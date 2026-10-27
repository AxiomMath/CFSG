module

public import Certificates.Data.Kernel.SmithD6.KcCheck

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

@[expose] noncomputable def nthB (l : List (Array Nat)) : Nat → Array Nat :=
  List.rec (motive := fun _ => Nat → Array Nat) (fun _ => #[])
    (fun a _ ih k => Nat.rec (motive := fun _ => Array Nat) a (fun k' _ => ih k') k) l

@[expose] noncomputable def d6PB (j : Nat) : Array Nat :=
  nthB (nthA J.pbC (Nat.div j 2048)) (Nat.mod j 2048)

@[expose] noncomputable def d6PP (j : Nat) : Array Nat :=
  nthB (nthA J.ppC (Nat.div j 2048)) (Nat.mod j 2048)

@[expose] noncomputable def kcRed (bs ps : List Nat) (x : Nat) : Nat := Nat.xor x (kcPick x bs ps)

@[expose] noncomputable def kcRedL (bs ps : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun b _ ih => kcRed bs ps b :: ih)

@[expose] noncomputable def kcZc : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => nIf(Nat.beq acc 0, 1, 0))
    (fun r _ ih acc => Nat.add (ih acc) (ih (Nat.xor acc r)))

@[expose] noncomputable def kcMeetN (bi bj pj : List Nat) : Nat := kcZc (kcRedL bj pj bi) 0

@[expose] noncomputable def kcMeetA (Bi Bj Pj : Array Nat) : Nat :=
  Array.rec (motive := fun _ => Nat) (fun bi => Array.rec (motive := fun _ => Nat)
    (fun bj => Array.rec (motive := fun _ => Nat) (fun pj => kcMeetN bi bj pj) Pj) Bj) Bi

@[expose] noncomputable def d6MeetK (i j : Nat) : Nat := kcMeetA (d6PB i) (d6PB j) (d6PP j)

end CFSG.KD.SmithD6

end
