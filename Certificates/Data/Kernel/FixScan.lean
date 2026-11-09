module

public import Certificates.Data.Kernel.SporSch.Co1VOrb
public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.FixScan

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KS.SporSch.VOrb

@[expose] noncomputable def allFixK (Ms : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun Mt _ ih => andB (Nat.beq (vmF (nat_lit 24) Mt x) x) ih) Ms

@[expose] noncomputable def fixScanK (T : Nat → Nat) (Ms : List Nat) (lo len : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (nIf(allFixK Ms (ptK T (Nat.add lo j)), Nat.succ acc, acc)) ih) len

@[expose] noncomputable def vmT (t o x : Nat) : Nat :=
  Nat.xor (fget t (Nat.add o (Nat.land x (nat_lit 255))) (nat_lit 24))
    (Nat.xor
      (fget t (Nat.add o (Nat.add (nat_lit 256) (Nat.land (Nat.shiftRight x (nat_lit 8)) (nat_lit 255))))
        (nat_lit 24))
      (fget t (Nat.add o (Nat.add (nat_lit 512) (Nat.land (Nat.shiftRight x (nat_lit 16)) (nat_lit 255))))
        (nat_lit 24)))

@[expose] noncomputable def tabOK (t o Mt : Nat) : Bool :=
  allN (nat_lit 768) fun j => Nat.beq (fget t (Nat.add o j) (nat_lit 24))
    (vmF (nat_lit 24) Mt (Nat.shiftLeft (Nat.mod j (nat_lit 256))
      (Nat.mul (nat_lit 8) (Nat.div j (nat_lit 256)))))

@[expose] noncomputable def allFixT (t : Nat) (os : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun o _ ih => andB (Nat.beq (vmT t o x) x) ih) os

@[expose] noncomputable def fixScanT (T : Nat → Nat) (t : Nat) (os : List Nat) (lo len : Nat) :
    Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (nIf(allFixT t os (ptK T (Nat.add lo j)), Nat.succ acc, acc)) ih) len

@[expose] noncomputable def fqXor (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) a (notB a) b

@[expose] noncomputable def fqVal (Qt x : Nat) : Bool := dotK (nat_lit 24) x (vecK (nat_lit 24) Qt x)

@[expose] noncomputable def fqPol (Qt x y : Nat) : Bool :=
  fqXor (dotK (nat_lit 24) x (vecK (nat_lit 24) Qt y)) (dotK (nat_lit 24) y (vecK (nat_lit 24) Qt x))

@[expose] noncomputable def fqRow (Qt f : Nat) (G : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g _ ih => Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (fqPol Qt f g))
      (Nat.mul (nat_lit 2) ih)) G

@[expose] noncomputable def fqGram (Qt : Nat) (F : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun f G ih => List.cons (Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (fqVal Qt f)) (Nat.mul (nat_lit 2) (fqRow Qt f G))) ih) F

@[expose] noncomputable def fqCount (E : List Nat) : Bool → Nat → Nat :=
  List.rec (motive := fun _ => Bool → Nat → Nat)
    (fun qa _ => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) qa)
    (fun m _ ih qa l => strictN (ih qa (Nat.shiftRight l (nat_lit 1))) fun a =>
      strictN (ih (fqXor qa (bit (Nat.xor l m) (nat_lit 0))) (Nat.shiftRight (Nat.xor l m) (nat_lit 1)))
        fun b => Nat.add a b) E

@[expose] noncomputable def fixKQ (d Mt Qt : Nat) (F Y : List Nat) (k a b : Nat) : Bool :=
  andB (Nat.beq (lenL F) k) (andB (Nat.beq (Nat.add (lenL Y) k) d)
  (andB (Nat.beq a (pw2 k))
  (andB (List.rec (motive := fun _ => Bool) true
      (fun f _ ih => andB (Nat.blt f (pw2 d)) (andB (Nat.beq (vecK d Mt f) f) ih)) F)
  (andB (pivK d F (nat_lit 0))
  (andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih => andB (Nat.blt y (pw2 d)) ih) Y)
  (andB (pivK d (List.rec (motive := fun _ => List Nat) List.nil
      (fun y _ ih => List.cons (Nat.xor (vecK d Mt y) y) ih) Y) (nat_lit 0))
    (Nat.beq (fqCount (fqGram Qt F) false (nat_lit 0)) b)))))))

end CFSG.KC.FixScan

end
