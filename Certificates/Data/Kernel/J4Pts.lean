module

public import Certificates.Data.Kernel.J4Fix

public section

namespace CFSG.KJ4.R

open CFSG.KJ4 CFSG.KJ4.S CFSG.KC.Loop

@[expose] noncomputable def ptsLet (c : Nat) : Bool :=
  orB (Nat.beq c (nat_lit 0)) (orB (Nat.beq c (nat_lit 2)) (Nat.beq c (nat_lit 5)))

@[expose] noncomputable def ptsStep (PT : Nat → Nat) (LET NOM e BM : Nat) : Nat :=
  strictN (Nat.land e (nat_lit 65535)) (fun i =>
  strictN (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 65535)) (fun p =>
  strictN (Nat.land (Nat.shiftRight e (nat_lit 32)) (nat_lit 15)) (fun c =>
    Bool.rec (motive := fun _ => Nat) BM (Nat.lor BM (Nat.shiftLeft (nat_lit 1) i))
      (andB (Nat.blt i NOM) (andB (Nat.blt p NOM)
      (andB (Nat.blt (nat_lit 0) (Nat.land BM (Nat.shiftLeft (nat_lit 1) p)))
      (andB (ptsLet c)
        (chkPtF (PT p) (letMat LET c) (PT i) (Nat.land (Nat.shiftRight e (nat_lit 36)) (nat_lit 7))))))))))

@[expose] noncomputable def ptsRun (PT : Nat → Nat) (LET NOM C m BM : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ BM => BM)
    (fun _ ih C BM => strictN C (fun C' => strictN (Nat.land C' (nat_lit 18446744073709551615)) (fun e =>
      strictN (ptsStep PT LET NOM e BM) (fun B => ih (Nat.shiftRight C' (nat_lit 64)) B)))) m C BM

@[expose] noncomputable def ptsL (PT : Nat → Nat) (LET NOM : Nat) (l : List Nat) (BM : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S =>
    strictN (ptsRun PT LET NOM (Nat.shiftRight C (nat_lit 12)) (Nat.land C (nat_lit 4095)) S) ih) l BM

@[expose] noncomputable def ptsWord (RT WT : Nat → Nat) (INV w : Nat) : Bool :=
  letB (WT w) (fun W => andB (Nat.blt (wR W) (nat_lit 12)) (wordOK RT INV W))

@[expose] noncomputable def j4Pts (k : KD) (PL : List Nat) : Bool :=
  andB (chkInv k.PS1 k.PS1)
  (andB (row11 (letMat k.LET (nat_lit 2))) (andB (row11 (letMat k.LET (nat_lit 5)))
  (andB (allIn k.nH (nat_lit 65536) (fun a => Nat.beq (k.HT a) (nat_lit 0)))
  (andB (allIn (nat_lit 0) (nat_lit 65536) (ptsWord k.RT k.WT k.INV))
    (Nat.beq (ptsL k.PT k.LET k.NOM PL (Nat.shiftLeft (nat_lit 1) k.i0)) (fullOf k))))))

end CFSG.KJ4.R

end
