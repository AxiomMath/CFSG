module

public import Certificates.Data.Kernel.F4Mat
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.M1F2

@[expose] noncomputable def crd (c i : Nat) : Nat := fget c i (nat_lit 2)

@[expose] noncomputable def hermK (c d : Nat) : Nat :=
  xorN (nat_lit 6) fun i => fm (crd c i) (sqC (crd d i))

@[expose] noncomputable def scaleK (a c : Nat) : Nat :=
  orN (nat_lit 6) fun i => Nat.shiftLeft (fm a (crd c i)) (Nat.mul (nat_lit 2) i)

@[expose] noncomputable def leadK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => (fun i => nIf(Nat.beq (crd c i) (nat_lit 0), acc, crd c i)) (Nat.sub (nat_lit 5) j))
    (nat_lit 6)

@[expose] noncomputable def normK (c : Nat) : Nat := strictN (leadK c) fun a => scaleK (sqC a) c

@[expose] noncomputable def tvK (v x : Nat) : Nat := Nat.xor x (scaleK (hermK x v) v)

@[expose] noncomputable def isPt (iso norm : Nat → Nat) (c : Nat) : Bool :=
  andB (notB (Nat.beq c (nat_lit 0))) (andB (Nat.beq (iso c) (nat_lit 0)) (Nat.beq (norm c) c))

@[expose] noncomputable def up (UP i : Nat) : Nat := fget UP i (nat_lit 12)

@[expose] noncomputable def pos (POS c : Nat) : Nat := fget POS c (nat_lit 10)

@[expose] noncomputable def ptsOK (iso norm : Nat → Nat) (UP POS : Nat) : Bool :=
  andB (allBelow (nat_lit 692) (nat_lit 11) fun i => Nat.blt (up UP i) (up UP (Nat.succ i)))
  (andB (allBelow (nat_lit 693) (nat_lit 11) fun i =>
      andB (isPt iso norm (up UP i)) (Nat.beq (pos POS (up UP i)) i))
    (allBelow (nat_lit 4096) (nat_lit 64) fun c =>
      bIf(isPt iso norm c, andB (Nat.blt (pos POS c) (nat_lit 693)) (Nat.beq (up UP (pos POS c)) c),
        Nat.beq (pos POS c) (nat_lit 693))))

@[expose] noncomputable def tvOK (wt : Nat → Bool) (UP TV : Nat) : Bool :=
  andB (Nat.beq (fget TV (nat_lit 45) (nat_lit 12)) (nat_lit 85))
    (Nat.beq (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i j => strictN j fun j => (fun c => nIf(wt c,
          nIf(Nat.beq (fget TV j (nat_lit 12)) c, Nat.succ j, nat_lit 100000), j)) (up UP i))
      (nat_lit 693)) (nat_lit 45))

@[expose] noncomputable def tabK (UP POS v p : Nat) : Nat := pos POS (normK (tvK v (up UP p)))

@[expose] noncomputable def letK (LT k : Nat) : Nat := fget LT k (nat_lit 6930)

@[expose] noncomputable def ap10 (P p : Nat) : Nat := fget P p (nat_lit 10)

@[expose] noncomputable def letOK (UP POS TV LT k : Nat) : Bool :=
  strictB (letK LT k) fun L => strictB (fget TV k (nat_lit 12)) fun v =>
  andB (Nat.beq (Nat.shiftRight L (nat_lit 6930)) (nat_lit 0))
    (allBelow (nat_lit 693) (nat_lit 11) fun p => strictB (ap10 L p) fun q =>
      andB (Nat.beq (tabK UP POS v p) q) (andB (Nat.blt q (nat_lit 693)) (Nat.beq (ap10 L q) p)))

end CFSG.KC.U6

end
