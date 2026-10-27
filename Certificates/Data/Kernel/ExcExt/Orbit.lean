module

public import Certificates.Data.Kernel.ExcExt.Twin

public section

namespace CFSG.ExcExtK

@[expose] noncomputable def ln32 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 32 i)) 4294967295

@[expose] noncomputable def reflA (K : KT) (u c a : Nat) : Nat :=
  ofDigK K.d fun k => Nat.add (digK c k) (Nat.mul 2 (Nat.mul a (hK K u k)))

@[expose] noncomputable def reflK (K : KT) (u c : Nat) : Nat :=
  reflA K u c (Nat.mod (sumN K.d fun j => Nat.mul (fK K u j) (digK c j)) 3)

@[expose] noncomputable def memK (c : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bor (Nat.beq a c) ih) L

@[expose] noncomputable def parE (e : Nat) : Nat := Nat.land e 65535

@[expose] noncomputable def refE (e : Nat) : Nat := Nat.land (Nat.shiftRight e 16) 255

@[expose] noncomputable def depE (e : Nat) : Nat := Nat.shiftRight e 24

@[expose] noncomputable def orbE (K : KT) (B : Nat) (reps : List Nat) (c e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (band (Nat.blt (parE e) (Nat.pow 3 K.d)) (band (Nat.blt (refE e) K.r)
      (band (Nat.blt (depE (ln32 B (parE e))) (depE e)) (Nat.beq (reflK K (refE e) (parE e)) c))))
    (memK c reps) (Nat.beq (depE e) 0)

@[expose] noncomputable def orbOK (K : KT) (B : Nat) (reps : List Nat) (c : Nat) : Bool :=
  orbE K B reps c (ln32 B c)

@[expose] noncomputable def orbRangeOK (K : KT) (B : Nat) (reps : List Nat) (lo n : Nat) : Bool :=
  allN n fun i => orbOK K B reps (Nat.add lo i)

end CFSG.ExcExtK

end
