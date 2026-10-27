module

public import Certificates.Data.Kernel.S23Inner

public section

namespace CFSG.KC.S23U

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.S23

@[expose] noncomputable def row20 (M t : Nat) : Nat := fget M t (nat_lit 20)

@[expose] noncomputable def act20 (M v : Nat) : Nat :=
  xorN (nat_lit 20) fun i => nIf(bit v i, row20 M i, nat_lit 0)

@[expose] noncomputable def rmul (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    orN (nat_lit 20) fun t => Nat.shiftLeft (act20 B (row20 A t)) (Nat.mul (nat_lit 20) t)

@[expose] noncomputable def ID20 : Nat :=
  orN (nat_lit 20) fun t => Nat.shiftLeft (pw2 t) (Nat.mul (nat_lit 20) t)

@[expose] noncomputable def wordR (G20 : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ID20
    (fun k _ ih => rmul (fget G20 k (nat_lit 400)) ih) w

@[expose] noncomputable def geomZero (G20 : Nat) (w : List Nat) : Bool :=
  strictB (wordR G20 w) fun M =>
    Nat.beq (Nat.land (Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft ID20 (nat_lit 400))
        (fun _ st => strictN st fun st =>
          Nat.lor (Nat.xor (Nat.land st (maskN (nat_lit 400))) (Nat.shiftRight st (nat_lit 400)))
            (Nat.shiftLeft (rmul (Nat.shiftRight st (nat_lit 400)) M) (nat_lit 400)))
        (nat_lit 11)) (maskN (nat_lit 400))) (nat_lit 0)

@[expose] noncomputable def xp (NP i : Nat) : Nat := fget NP i (nat_lit 72)

@[expose] noncomputable def powsOK (B6 NP : Nat) : Bool :=
  andB (Nat.beq (xp NP (nat_lit 0)) ONE)
  (andB (Nat.beq (xp NP (nat_lit 1)) (mmul (mmul (mmul (mmul (fget B6 (nat_lit 0) (nat_lit 72))
      (fget B6 (nat_lit 3) (nat_lit 72))) (fget B6 (nat_lit 4) (nat_lit 72)))
      (fget B6 (nat_lit 7) (nat_lit 72))) (fget B6 (nat_lit 16) (nat_lit 72))))
  (andB (allN (nat_lit 5) fun i => Nat.beq (xp NP (Nat.succ i)) (mmul (xp NP i) (xp NP (nat_lit 1))))
  (andB (Nat.beq (mmul (mmul (xp NP (nat_lit 5)) (xp NP (nat_lit 5))) (xp NP (nat_lit 1))) ONE)
    (notB (Nat.beq (tr (xp NP (nat_lit 1))) (tr (barM (xp NP (nat_lit 1)))))))))

@[expose] noncomputable def cycOK (NP CV : Nat) : Bool :=
  Nat.beq (mmul CV (mk fun i j => ent (xp NP i) (nat_lit 0) j)) ONE

@[expose] noncomputable def smul (a P : Nat) : Nat := strictN P fun P => mk fun i j => fm a (ent P i j)

@[expose] noncomputable def defect (A : Nat) : Nat := Nat.xor A (Nat.mul (ent A (nat_lit 0) (nat_lit 0)) ONE)

@[expose] noncomputable def xpow (NP k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun _ ih => mmul ih (xp NP (nat_lit 1))) k

@[expose] noncomputable def basisT (NP : Nat) (sq : Bool) : Nat :=
  orN (nat_lit 12) fun b => Nat.shiftLeft
    (Bool.rec (motive := fun _ => Nat)
      (smul (Nat.succ (Nat.land b (nat_lit 1))) (xpow NP (Nat.shiftRight b (nat_lit 1))))
      (smul (sqC (Nat.succ (Nat.land b (nat_lit 1)))) (xpow NP (Nat.mul (nat_lit 2) (Nat.shiftRight b (nat_lit 1)))))
      sq)
    (Nat.mul (nat_lit 72) b)

@[expose] noncomputable def xsum (T c : Nat) : Nat :=
  xorN (nat_lit 12) fun b => nIf(bit c b, fget T b (nat_lit 72), nat_lit 0)

@[expose] noncomputable def scalOK (NP : Nat) : Bool :=
  strictB (basisT NP true) fun TS => strictB (basisT NP false) fun T =>
    allBelow (nat_lit 4096) (nat_lit 64) fun c =>
      orB (notB (Nat.beq (defect (xsum TS c)) (nat_lit 0))) (Nat.beq (defect (xsum T c)) (nat_lit 0))

@[expose] noncomputable def bindRowW (M w n : Nat) (r : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun t => Nat.beq t n)
    (fun x _ ih t => andB (Nat.blt x (pw2 w)) (andB (Nat.beq x (fget M t w)) (ih (Nat.succ t))))
    r (nat_lit 0)

@[expose] noncomputable def bindW (P w n cnt : Nat) (A : Array (Array Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k cnt)
    (fun r _ ih k => andB (bindRowW (fget P k (Nat.mul w n)) w n r.toList) (ih (Nat.succ k)))
    A.toList (nat_lit 0)

end CFSG.KC.S23U

end
