module

public import Certificates.Data.Kernel.BfsPin
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.PermPinK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def memK (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false
    (allN N fun j => Bool.rec (motive := fun _ => Bool) true false (Nat.beq x (T j)))

@[expose] noncomputable def fixK (w : Nat) (ps : List Nat) (P : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => Bool.rec (motive := fun _ => Bool) false ih (Nat.beq (pg w (mask w) P p) p)) ps

@[expose] noncomputable def stabK (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (t : Nat) :
    Bool :=
  strictB (pidn n w) fun I => allN N fun k => strictB (T k) fun g =>
    Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool) (Nat.beq g t) true (Nat.beq g I)) (fixK w ps g)

@[expose] noncomputable def centCnt (n w N : Nat) (T : Nat → Nat) (t : Nat) : Nat :=
  foldN N (fun j s => strictN (T j) fun g =>
    Bool.rec (motive := fun _ => Nat) s (Nat.succ s)
      (Nat.beq (pcomp n w (mask w) g t) (pcomp n w (mask w) t g))) (nat_lit 0)

end CFSG.KC.PermPinK

end
