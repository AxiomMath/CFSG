module

public import Certificates.Data.Kernel.SporSch.Co1MatW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KC.Co1B

@[expose] noncomputable def encLetterK (j : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => Nat.add n n)
    (fun n => Nat.succ (Nat.add (Nat.succ n) (Nat.succ n))) j

@[expose] noncomputable def encWordK (w : List Int) : List Nat := w.map encLetterK

@[expose] noncomputable def powWM (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idM (fun _ ih => strictN ih (fun Y => mulWK Y X)) e

@[expose] noncomputable def heisK (T X XI Y YI : Nat) : Bool :=
  strictB (mulWK (mulWK (mulWK XI YI) X) Y) (fun W =>
    bAnd(invOKW X XI, bAnd(invOKW Y YI,
    bAnd(Nat.beq (powWM X 5) idM, bAnd(Nat.beq (powWM Y 5) idM,
    bAnd(Nat.beq (powWM W 5) idM, bAnd(Nat.beq (Nat.shiftRight W 576) 0,
    bAnd(bIf(Nat.beq W idM, false, true),
    bAnd(Nat.beq (mulWK X W) (mulWK W X), bAnd(Nat.beq (mulWK Y W) (mulWK W Y),
    bAnd(Nat.beq (mulWK T T) idM, Nat.beq (mulWK (mulWK T X) T) XI)))))))))))

@[expose] noncomputable def dihK (T C CI : Nat) : Bool :=
  strictB (mulWK T (mulWK C (mulWK T CI))) (fun P =>
    bAnd(invOKW C CI, bAnd(Nat.beq (powWM P 13) idM,
    bAnd(Nat.beq (Nat.shiftRight P 576) 0, bIf(Nat.beq P idM, false, true)))))

end CFSG.KS.SporSch.M24

end
