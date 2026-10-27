module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.M24L2

open CFSG.KC.Loop

@[expose] noncomputable def nib (m k : Nat) : Nat :=
  fld(m, Nat.shiftLeft k (nat_lit 2), nat_lit 15)

@[expose] noncomputable def bitM (x j y : Nat) : Nat := Nat.mul (fld(x, j, nat_lit 1)) y

@[expose] noncomputable def lap (m x : Nat) : Nat :=
  Nat.xor (Nat.xor (bitM x (nat_lit 0) (nib m (nat_lit 0))) (bitM x (nat_lit 1) (nib m (nat_lit 1))))
    (Nat.xor (bitM x (nat_lit 2) (nib m (nat_lit 2))) (bitM x (nat_lit 3) (nib m (nat_lit 3))))

@[expose] noncomputable def aff (c x : Nat) : Nat :=
  Nat.xor (Nat.land c (nat_lit 15)) (lap (Nat.shiftRight c (nat_lit 4)) x)

@[expose] noncomputable def packN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v _ ih => Nat.lor v (Nat.shiftLeft ih (nat_lit 4))) l

@[expose] noncomputable def allL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(p a, ih)) L

@[expose] noncomputable def anyL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(p a, true, ih)) L

@[expose] noncomputable def foldL {α β : Type} (f : β → α → β) (L : List α) (s : β) : β :=
  List.rec (motive := fun _ => β → β) (fun s => s) (fun a _ ih s => ih (f s a)) L s

@[expose] noncomputable def fldT (T y : Nat) : Nat :=
  fld(T, Nat.shiftLeft y (nat_lit 2), nat_lit 15)

@[expose] noncomputable def lapT (m : Nat) : Nat :=
  strictN (nib m (nat_lit 0)) fun n0 => strictN (nib m (nat_lit 1)) fun n1 =>
  strictN (nib m (nat_lit 2)) fun n2 => strictN (nib m (nat_lit 3)) fun n3 =>
  strictN (Nat.xor n0 n1) fun n01 => strictN (Nat.xor n2 n3) fun n23 =>
  packN [nat_lit 0, n0, n1, n01, n2, Nat.xor n0 n2, Nat.xor n1 n2, Nat.xor n01 n2,
    n3, Nat.xor n0 n3, Nat.xor n1 n3, Nat.xor n01 n3,
    n23, Nat.xor n0 n23, Nat.xor n1 n23, Nat.xor n01 n23]

@[expose] noncomputable def mulC (a b : Nat) : Nat :=
  strictN (lapT (Nat.shiftRight a (nat_lit 4))) fun T => strictN (Nat.shiftRight b (nat_lit 4)) fun mb =>
  Nat.lor (Nat.xor (Nat.land a (nat_lit 15)) (fldT T (Nat.land b (nat_lit 15))))
    (Nat.shiftLeft (Nat.lor (fldT T (nib mb (nat_lit 0)))
      (Nat.shiftLeft (Nat.lor (fldT T (nib mb (nat_lit 1)))
        (Nat.shiftLeft (Nat.lor (fldT T (nib mb (nat_lit 2)))
          (Nat.shiftLeft (fldT T (nib mb (nat_lit 3))) (nat_lit 4))) (nat_lit 4))) (nat_lit 4)))
      (nat_lit 4))

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (mulC a b) (mulC b a)

@[expose] noncomputable def idC : Nat := nat_lit 541200

@[expose] noncomputable def codeF (f : Nat → Nat) : Nat :=
  Nat.add (f (nat_lit 0)) (Nat.mul (nat_lit 16) (Nat.add (Nat.xor (f (nat_lit 1)) (f (nat_lit 0)))
    (Nat.mul (nat_lit 16) (Nat.add (Nat.xor (f (nat_lit 2)) (f (nat_lit 0)))
      (Nat.mul (nat_lit 16) (Nat.add (Nat.xor (f (nat_lit 4)) (f (nat_lit 0)))
        (Nat.mul (nat_lit 16) (Nat.xor (f (nat_lit 8)) (f (nat_lit 0))))))))))

@[expose] noncomputable def isTC (c : Nat) : Bool := Nat.beq (Nat.shiftRight c (nat_lit 4)) (nat_lit 33825)

end CFSG.KC.M24L2
