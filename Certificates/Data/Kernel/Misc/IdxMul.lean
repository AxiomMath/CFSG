module

public import Certificates.Data.Kernel.Misc.ConjTab

public section

namespace CFSG.KC.Misc.IdxMul

open CFSG.KC.Enum (pg pcomp pidn permOK)
open CFSG.KS (mask)
open CFSG.KC.Loop (strictN)
open CFSG.KC.Ord (andB orB notB)
open CFSG.KC.LQT.P (allN anyN letB impB)
open CFSG.KC.Misc.ConjTab (cj3)

@[expose] noncomputable def stepF (b d T x k : Nat) : Nat :=
  pg b (mask b) T (Nat.add (Nat.mul d x) k)

@[expose] noncomputable def mulK (b c d T PL : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun i _ => i)
    (fun _ ih i j => nIf(Nat.beq j (nat_lit 0), i,
      strictN (pg c (mask c) PL j) fun r =>
        strictN (ih i (Nat.div r d)) fun x => stepF b d T x (Nat.mod r d))) f

@[expose] noncomputable def powK (M : Nat → Nat → Nat) (i e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ acc => strictN acc fun a => M a i) e

@[expose] noncomputable def ndMask (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun p _ ih m => nIf(Nat.beq (Nat.land (Nat.shiftRight m p) (nat_lit 1)) (nat_lit 0),
      ih (Nat.lor m (Nat.shiftLeft (nat_lit 1) p)), nat_lit 0)) l

@[expose] noncomputable def ordAt (M : Nat → Nat → Nat) (ob O nO i : Nat) : Bool :=
  impB (andB (Nat.beq (powK M i 4) (nat_lit 0)) (notB (Nat.beq (powK M i 2) (nat_lit 0))))
    (anyN nO fun a => Nat.beq (pg ob (mask ob) O a) i)

@[expose] noncomputable def prods4 (M : Nat → Nat → Nat) (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    List Nat :=
  [M a0 b0, M a0 b1, M a0 b2, M a0 b3, M a1 b0, M a1 b1, M a1 b2, M a1 b3,
    M a2 b0, M a2 b1, M a2 b2, M a2 b3, M a3 b0, M a3 b1, M a3 b2, M a3 b3]

@[expose] noncomputable def pairAt (M : Nat → Nat → Nat) (AM : Nat → Nat) (nA i j : Nat) : Bool :=
  orB (notB (Nat.beq (M i j) (M j i)))
    (letB (ndMask (prods4 M (powK M i 0) (powK M i 1) (powK M i 2) (powK M i 3)
        (powK M j 0) (powK M j 1) (powK M j 2) (powK M j 3)) (nat_lit 0)) fun r =>
      orB (Nat.beq r (nat_lit 0)) (anyN nA fun a => Nat.beq r (AM a)))

@[expose] noncomputable def pairRow (M : Nat → Nat → Nat) (AM : Nat → Nat) (nA ob O nO a : Nat) :
    Bool :=
  allN nO fun b => pairAt M AM nA (pg ob (mask ob) O a) (pg ob (mask ob) O b)

@[expose] noncomputable def bitB (m x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m x) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def plAt (c d pb PL Par f : Nat) (P : List (List Int)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih j => andB (andB (andB (Nat.blt w.length f)
        (w.all fun l => decide (1 ≤ l ∧ l ≤ (d : Int))))
      (impB (notB (Nat.beq j (nat_lit 0)))
        (Nat.beq (pg c (mask c) PL j)
          (Nat.add (Nat.mul d (pg pb (mask pb) Par j)) (Nat.sub (w.getLastD 0).toNat 1)))))
      (ih (Nat.succ j))) P

@[expose] noncomputable def witK (n w kP : Nat) (P PI L LI K : Nat → Nat) (s a : Nat)
    (cw : List Int) (sign : Bool) (c ci t ti : Nat) : Bool :=
  andB (CFSG.KS.Prim.wordEqK n w (mask w) (pidn n w) P PI kP cw c)
  (andB (permOK n w (mask w) (n * w) c ci)
  (andB (permOK n w (mask w) (n * w) t ti)
  (andB (Nat.beq t (pcomp n w (mask w) ci (cj3 n w (L a) c (LI a))))
  (andB (Nat.beq (cj3 n w (L s) c (LI s)) c)
  (letB (Bool.rec (motive := fun _ => Nat) ti t sign) fun v =>
    andB (Nat.beq (pcomp n w (mask w) v v) (pidn n w))
    (andB (anyN n fun x => notB (Nat.beq (pg w (mask w) v x) x))
    (andB (Nat.beq (pcomp n w (mask w) v (K 0)) (pcomp n w (mask w) (K 0) v))
      (Nat.beq (pcomp n w (mask w) v (K 1)) (pcomp n w (mask w) (K 1) v)))))))))

@[expose] noncomputable def witL (n w kP : Nat) (P PI L LI K : Nat → Nat) (s a : Nat)
    (cw : List Int) (sign : Bool) : Bool :=
  letB (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) P PI cw) fun c =>
  letB (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) P PI (cw.reverse.map fun l => -l)) fun ci =>
  letB (pcomp n w (mask w) ci (cj3 n w (L a) c (LI a))) fun t =>
  letB (pcomp n w (mask w) (cj3 n w (L a) ci (LI a)) c) fun ti =>
    witK n w kP P PI L LI K s a cw sign c ci t ti

end CFSG.KC.Misc.IdxMul

end
