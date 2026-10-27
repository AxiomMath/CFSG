module

public import Certificates.Data.Kernel.U6.Sbar

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def keyA (A m : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (subImg A m (nat_lit 1)) (nat_lit 1024))
    (subImg A m (nat_lit 3))) (nat_lit 1024)) (subImg A m (nat_lit 45))

@[expose] noncomputable def AK (A : Nat) : Nat :=
  sumBelow (nat_lit 512) (nat_lit 8) fun m => Nat.shiftLeft (keyA A m) (Nat.mul (nat_lit 30) m)

@[expose] noncomputable def maskOf (AKs k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 512)
    (fun i acc => (fun m => nIf(Nat.beq (fget AKs m (nat_lit 30)) k, m, acc))
      (Nat.sub (nat_lit 511) i))
    (nat_lit 512)

@[expose] noncomputable def matX (A AKs X XI : Nat) : Nat :=
  sumN (nat_lit 9) fun i => strictN (elt A i) fun a =>
    Nat.shiftLeft (maskOf AKs (Nat.add (Nat.mul (Nat.add
        (Nat.mul (ap10 X (ap10 a (ap10 XI (nat_lit 1)))) (nat_lit 1024))
        (ap10 X (ap10 a (ap10 XI (nat_lit 3))))) (nat_lit 1024))
      (ap10 X (ap10 a (ap10 XI (nat_lit 45))))))
      (Nat.mul (nat_lit 9) i)

@[expose] noncomputable def redV (B x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i y => strictN y fun y => (fun p =>
      nIf(andB (Nat.beq (fget y p (nat_lit 1)) (nat_lit 1))
          (notB (Nat.beq (fget B p (nat_lit 9)) (nat_lit 0))),
        Nat.xor y (fget B p (nat_lit 9)), y)) (Nat.sub (nat_lit 8) i))
    (nat_lit 9)

@[expose] noncomputable def leadV (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => nIf(Nat.beq (fget x i (nat_lit 1)) (nat_lit 1), i, acc)) (nat_lit 9)

@[expose] noncomputable def insV (B x : Nat) : Nat :=
  strictN (redV B x) fun r =>
    nIf(Nat.beq r (nat_lit 0), B, Nat.lor B (Nat.shiftLeft r (Nat.mul (nat_lit 9) (leadV r))))

@[expose] noncomputable def inImg (X v : Nat) : Bool :=
  strictB (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i B => strictN B fun B => insV B (Nat.xor (fget X i (nat_lit 9)) (pw2 i)))
      (nat_lit 9)) fun B =>
    Nat.beq (redV B v) (nat_lit 0)

@[expose] noncomputable def matT (A AKs : Nat) (TR TRI : Nat → Nat) (o k : Nat) : Nat :=
  matX A AKs (TR (Nat.add o k)) (TRI (Nat.add o k))

@[expose] noncomputable def matsT (A AKs : Nat) (TR TRI : Nat → Nat) (o m : Nat) : Nat :=
  sumN m fun k => Nat.shiftLeft (matT A AKs TR TRI o k) (Nat.mul (nat_lit 81) k)

@[expose] noncomputable def centK (A : Nat) (TR TRI : Nat → Nat) (o0 o1 o2 : Nat) : Bool :=
  strictB (AK A) fun AKs =>
  strictB (matsT A AKs TR TRI o0 (nat_lit 21)) fun MA =>
  strictB (matsT A AKs TR TRI o1 (nat_lit 16)) fun MB =>
  strictB (matsT A AKs TR TRI o2 (nat_lit 60)) fun MC =>
    allN (nat_lit 21) fun a =>
      allN (nat_lit 16) fun b => strictB (mcomp (mt MA a) (mt MB b)) fun Mab =>
        allN (nat_lit 60) fun c => strictB (mcomp Mab (mt MC c)) fun M =>
          andB (orB (notB (Nat.beq M mId))
              (andB (Nat.beq a (nat_lit 0)) (andB (Nat.beq b (nat_lit 0)) (Nat.beq c (nat_lit 0)))))
            (orB (notB (Nat.beq (mapV M (nat_lit 19)) (nat_lit 19)))
              (orB (notB (Nat.beq (mcomp M M) mId)) (notB (inImg M (nat_lit 19)))))

end CFSG.KC.U6

end
