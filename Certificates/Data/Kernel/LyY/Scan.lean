module

public import Certificates.Data.Kernel.J2Enum

public section

namespace CFSG.KC.LyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3 CFSG.KC.J2Enum CFSG.KS.Mathieu

@[expose] noncomputable def letP (x xi f g : Nat → Nat) (c p : Nat) : Nat :=
  nIf(Nat.beq (Nat.shiftRight c (nat_lit 1)) (nat_lit 1),
    nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), x p, xi p),
    nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), f p, g p))

@[expose] noncomputable def wP (x xi f g : Nat → Nat) (wd : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun z _ ih p => strictN (ih p) (fun q => letP x xi f g (icode z) q)) wd

@[expose] noncomputable def idW (w m BP : Nat) (x xi f g : Nat → Nat) (wd : List Int) : Bool :=
  bAnd(Nat.beq (wP x xi f g wd (pg w m BP (nat_lit 0))) (pg w m BP (nat_lit 0)),
    bAnd(Nat.beq (wP x xi f g wd (pg w m BP (nat_lit 1))) (pg w m BP (nat_lit 1)),
      Nat.beq (wP x xi f g wd (pg w m BP (nat_lit 2))) (pg w m BP (nat_lit 2))))

@[expose] noncomputable def relB (w m BP : Nat) (x xi f g : Nat → Nat) (R W : List (List Int)) :
    Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true (fun wd _ ih => bAnd(idW w m BP x xi f g wd, ih)) R,
    List.rec (motive := fun _ => Bool) true
      (fun wd _ ih => bAnd(bIf(idW w m BP x xi f g wd, false, true), ih)) W)

@[expose] noncomputable def contribY (w m BP : Nat) (x xi f g : Nat → Nat) (R W : List (List Int)) :
    Nat :=
  Nat.add (nIf(ord12B w m BP f, nIf(relB w m BP x xi f g R W, nat_lit 1, nat_lit 0), nat_lit 0))
    (nIf(ordB w m BP f (nat_lit 2), Nat.shiftLeft (nat_lit 1) (nat_lit 20), nat_lit 0))

@[expose] noncomputable def blkY (n w : Nat) (LR TR TRI : Nat → Nat) (BP X XI : Nat)
    (R W : List (List Int)) (a : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun L0 => strictN (LR (nat_lit 1)) (fun L1 =>
  strictN (LR (nat_lit 2)) (fun L2 =>
  strictN (TR (Nat.add (roff n (Nat.mul n w) L0) a)) (fun t0 =>
  strictN (TRI (Nat.add (roff n (Nat.mul n w) L0) a)) (fun t0i =>
  sumF (rcnt L1) (fun b => strictN (TR (Nat.add (roff n (Nat.mul n w) L1) b)) (fun t1 =>
    strictN (TRI (Nat.add (roff n (Nat.mul n w) L1) b)) (fun t1i =>
    sumF (rcnt L2) (fun c => strictN (TR (Nat.add (roff n (Nat.mul n w) L2) c)) (fun t2 =>
      strictN (TRI (Nat.add (roff n (Nat.mul n w) L2) c)) (fun t2i =>
      contribY w (mask w) BP (fun p => pg w (mask w) X p) (fun p => pg w (mask w) XI p)
        (fun p => pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 p)))
        (fun p => pg w (mask w) t2i (pg w (mask w) t1i (pg w (mask w) t0i p))) R W)))))))))))

@[expose] noncomputable def conjKey (w BP X t0 t1 t2 t0i t1i t2i : Nat) : Nat :=
  (fun (h : Nat → Nat) => Nat.lor (h (pg w (mask w) BP (nat_lit 2)))
    (Nat.lor (Nat.shiftLeft (h (pg w (mask w) BP (nat_lit 1))) w)
      (Nat.shiftLeft (h (pg w (mask w) BP (nat_lit 0))) (Nat.mul (nat_lit 2) w))))
  fun p => pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 (pg w (mask w) X
    (pg w (mask w) t2i (pg w (mask w) t1i (pg w (mask w) t0i p))))))

@[expose] noncomputable def fixCnt (n : Nat) (f : Nat → Nat) : Nat :=
  sumF n (fun p => nIf(Nat.beq (f p) p, nat_lit 1, nat_lit 0))

end CFSG.KC.LyY

end
