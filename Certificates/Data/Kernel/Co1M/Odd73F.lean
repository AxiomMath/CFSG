module

public import Certificates.Data.Kernel.Co1M.Odd73
public import Certificates.Data.Kernel.Co1Odd71
public import Certificates.Data.Kernel.Co1FixList

public section

namespace CFSG.KC.Odd73

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def faithK (TA TB : Nat) (P V : List Nat) : Bool :=
  andB (Nat.beq (lenL V) (lenL P)) (allN (lenL P) fun i =>
    orB (Nat.beq (getL (nat_lit 0) P i) (idF (nat_lit 24)))
    ((fun v => andB (Nat.blt v (pw2 (nat_lit 24))) (andB (Nat.beq (vmF (nat_lit 24) TA v) v)
      (andB (Nat.beq (vmF (nat_lit 24) TB v) v)
        (notB (Nat.beq (vmF (nat_lit 24) (trK (nat_lit 24) (getL (nat_lit 0) P i)) v) v)))))
      (getL (nat_lit 0) V i)))

@[expose] noncomputable def offK (F : List Nat) (m j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b ih => nIf(bit j b, Nat.xor ih (getL (nat_lit 0) F b), ih)) m

@[expose] noncomputable def ind7K (t4 : Nat → Bool) (T0 T1 T2 x : Nat) : Nat :=
  (fun a => (fun f0 f1 f2 =>
    Nat.add a (Nat.add (Nat.shiftLeft (nIf(f0, nat_lit 1, nat_lit 0)) (nat_lit 12))
      (Nat.add (Nat.shiftLeft (nIf(andB f0 (Nat.beq a (nat_lit 1)), nat_lit 1, nat_lit 0))
        (nat_lit 24))
      (Nat.add (Nat.shiftLeft (nIf(f1, nat_lit 1, nat_lit 0)) (nat_lit 36))
      (Nat.add (Nat.shiftLeft (nIf(andB f1 (Nat.beq a (nat_lit 1)), nat_lit 1, nat_lit 0))
        (nat_lit 48))
      (Nat.add (Nat.shiftLeft (nIf(f2, nat_lit 1, nat_lit 0)) (nat_lit 60))
        (Nat.shiftLeft (nIf(andB f2 (Nat.beq a (nat_lit 1)), nat_lit 1, nat_lit 0))
          (nat_lit 72))))))))
    (Nat.beq (vmF (nat_lit 24) T0 x) x) (Nat.beq (vmF (nat_lit 24) T1 x) x)
    (Nat.beq (vmF (nat_lit 24) T2 x) x))
  (nIf(t4 x, nat_lit 1, nat_lit 0))

@[expose] noncomputable def cnt7K (t4 : Nat → Bool) (T0 T1 T2 : Nat) (F : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => ind7K t4 T0 T1 T2 acc)
    (fun f _ ih acc => CFSG.KC.Loop.strictN (ih acc) fun a =>
      CFSG.KC.Loop.strictN (ih (Nat.xor acc f)) fun b => Nat.add a b) F

@[expose] noncomputable def pack7 (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.add a (Nat.shiftLeft ih (nat_lit 12))) L

end CFSG.KC.Odd73

end
