module

public import CFSG.Certificates.Kernel.Orders.Mat
public import Certificates.Data.Kernel.SporSch.LyMat

public section

namespace CFSG.KC.Misc.HNHeis

open CFSG.KC.Ord CFSG.KS.SporSch.LyM

@[expose] noncomputable def LH : Nat := rep1 13 (Nat.mul 133 133)

@[expose] noncomputable def HH : Nat := Nat.shiftLeft LH 12

@[expose] noncomputable def CMH : Nat := Nat.mul (Nat.sub (Nat.shiftLeft 1 13) 1) (rep1 1729 133)

@[expose] noncomputable def RMH : Nat := Nat.sub (Nat.shiftLeft 1 1729) 1

@[expose] noncomputable def ONEH : Nat := rep1 1742 133

@[expose] noncomputable def LVH : Nat := rep1 13 133

@[expose] noncomputable def HVH : Nat := Nat.shiftLeft LVH 12

@[expose] noncomputable def constsH : Bool := constsOK 5 13 1729 133 9 LH HH CMH RMH ONEH LVH HVH

@[expose] noncomputable def mulH (X Y : Nat) : Nat := mulR 5 13 1729 133 9 LH HH CMH RMH X Y

@[expose] noncomputable def vldH (X : Nat) : Bool := validM 5 229957 LH HH X

@[expose] noncomputable def regH (R : List Nat) (i : Nat) : Nat := R.getD i ONEH

@[expose] noncomputable def wordFromH (R : List Nat) (P : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun P => P)
    (fun l _ ih P => CFSG.KC.Loop.strictN (mulH P (regH R (Nat.sub l 1))) ih) w P

@[expose] noncomputable def wordH (R : List Nat) (w : List Nat) : Nat := wordFromH R ONEH w

@[expose] noncomputable def letL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def slpFromH (R : List Nat) (prog : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R)
    (fun w _ ih R => letL (wordH R w) fun x => ih (R ++ [x])) prog R

@[expose] noncomputable def slpH (A B : Nat) (prog : List (List Nat)) : List Nat :=
  slpFromH [A, B] prog

@[expose] noncomputable def relH (R : List Nat) (u v : List Nat) : Bool :=
  Nat.beq (wordH R u) (wordH R v)

end CFSG.KC.Misc.HNHeis

end
