module

public import Certificates.Kernel.E27J3Syl.KF
public import Certificates.Kernel.E27J3Syl.K

public section

namespace CFSG.KD.E27J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def jTr (wd : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ ih => strictN ih (fun y => pg 13 (mask 13) (jA l) y)) wd

@[expose] noncomputable def jWBL (wd : List Nat) (P : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (jTr wd b) (pg 13 (mask 13) P b), ih)) L

@[expose] noncomputable def jWB (wd : List Nat) (P : Nat) : Bool := jWBL wd P bsC

end CFSG.KD.E27J3S

end
