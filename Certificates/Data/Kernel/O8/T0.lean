module

public import Certificates.Data.Kernel.O8.S0
public import Certificates.Data.Kernel.O8.Z4

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def POPT : Nat :=
  orN (nat_lit 64) fun x => Nat.shiftLeft (popc (nat_lit 6) x) (Nat.mul (nat_lit 3) x)

@[expose] noncomputable def pc6 (P x : Nat) : Nat := fget P x (nat_lit 3)

@[expose] noncomputable def sliceK (A : Nat) : Nat :=
  strictN A fun A => orN (nat_lit 6) fun i => Nat.shiftLeft
    (Nat.add (orN (nat_lit 6) fun k => Nat.shiftLeft (bitN (ent4 A i k) (nat_lit 0)) k)
      (Nat.shiftLeft (orN (nat_lit 6) fun k => Nat.shiftLeft (bitN (ent4 A i k) (nat_lit 1)) k) (nat_lit 6)))
    (Nat.mul (nat_lit 12) i)

@[expose] noncomputable def ltK (G C : Nat) (ws : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun w _ ih i => Nat.lor (Nat.shiftLeft (sliceK (prod4K G C w)) (Nat.mul (nat_lit 72) i))
      (ih (Nat.succ i)))
    ws (nat_lit 0)

@[expose] noncomputable def mvB (P A v : Nat) : Nat :=
  (fun v0 v1 => orN (nat_lit 6) fun i => (fun lo hi => (fun c => Nat.lor (Nat.shiftLeft (Nat.land c (nat_lit 1)) i)
        (Nat.shiftLeft (Nat.xor (bitN c (nat_lit 1))
          (Nat.land (Nat.xor (pc6 P (Nat.land hi v0)) (pc6 P (Nat.land lo v1))) (nat_lit 1)))
          (Nat.add (nat_lit 6) i)))
      (pc6 P (Nat.land lo v0)))
    (fget A (Nat.mul (nat_lit 2) i) (nat_lit 6)) (fget A (Nat.succ (Nat.mul (nat_lit 2) i)) (nat_lit 6)))
    (Nat.land v (nat_lit 63)) (Nat.shiftRight v (nat_lit 6))

@[expose] noncomputable def addB (v w : Nat) : Nat :=
  (fun a0 a1 b0 b1 => Nat.add (Nat.xor a0 b0) (Nat.shiftLeft (Nat.xor (Nat.xor a1 b1) (Nat.land a0 b0)) (nat_lit 6)))
    (Nat.land v (nat_lit 63)) (Nat.shiftRight v (nat_lit 6)) (Nat.land w (nat_lit 63)) (Nat.shiftRight w (nat_lit 6))

@[expose] noncomputable def negB (v : Nat) : Nat :=
  Nat.xor v (Nat.shiftLeft (Nat.land v (nat_lit 63)) (nat_lit 6))

@[expose] noncomputable def tmulK (P LT MT g h : Nat) : Nat :=
  (fun gv gt gs hv ht hs => strictN (mvB P (fget LT gs (nat_lit 72)) hv) fun w =>
      Nat.add (addB gv (nIf(Nat.beq gt (nat_lit 1), negB w, w)))
        (Nat.add (Nat.mul (nat_lit 4096) (Nat.xor gt ht)) (Nat.mul (nat_lit 8192) (tget MT gs hs))))
    (Nat.land g (nat_lit 4095)) (bitN g (nat_lit 12)) (Nat.shiftRight g (nat_lit 13))
    (Nat.land h (nat_lit 4095)) (bitN h (nat_lit 12)) (Nat.shiftRight h (nat_lit 13))

@[expose] noncomputable def wordsOK (G L : Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 64))
    (fun w _ ih i => andB (lettersOK w) (andB (Nat.beq (wordRowsK G w) (mat L i)) (ih (Nat.succ i))))
    ws (nat_lit 0)

@[expose] noncomputable def e0OK (L : Nat) : Bool :=
  allN (nat_lit 64) fun i => Nat.beq (bvecK (mat L i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def t0Gen (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 3), Nat.shiftLeft (nat_lit 64) k, Nat.mul (nat_lit 8192) (Nat.add k (nat_lit 1)))

@[expose] noncomputable def t0At (P LT MT x k : Nat) : Bool :=
  andB (Nat.blt k (nat_lit 6)) (notB (Nat.beq (tmulK P LT MT x (t0Gen k)) (tmulK P LT MT (t0Gen k) x)))

@[expose] noncomputable def qes (c : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (Nat.land c (nat_lit 63)) (nat_lit 6)) (Nat.mul (nat_lit 4096) (Nat.shiftRight c (nat_lit 6)))

@[expose] noncomputable def t0OK (LT MT YW : Nat) : Bool :=
  Nat.beq (nat_lit 1) (strictN LT fun LT => strictN POPT fun P =>
    nIf(allBelow (nat_lit 8192) (nat_lit 128) fun c =>
      Nat.beq (nat_lit 1) (strictN (tmulK P LT MT (nat_lit 1) (qes c))
        fun x => nIf(t0At P LT MT x (fget YW c (nat_lit 3)), nat_lit 1, nat_lit 0)), nat_lit 1, nat_lit 0))

@[expose] noncomputable def commAt (P LT MT g : Nat) : Bool :=
  Nat.beq (nat_lit 1) (strictN (tmulK P LT MT (nat_lit 1537) g) fun l =>
    strictN (tmulK P LT MT g (nat_lit 1537)) fun r =>
      nIf(orB (Nat.beq l r) (Nat.beq l (tmulK P LT MT r (nat_lit 64))), nat_lit 1, nat_lit 0))

@[expose] noncomputable def commOK (LT MT : Nat) : Bool :=
  Nat.beq (nat_lit 1) (strictN LT fun LT => strictN POPT fun P =>
    nIf(allBelow (nat_lit 8192) (nat_lit 128) fun c => commAt P LT MT (qes c), nat_lit 1, nat_lit 0))

end CFSG.KC.O8

end
