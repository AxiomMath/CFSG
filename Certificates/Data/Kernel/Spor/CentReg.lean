module

public import Certificates.Data.Kernel.Spor.PChain

public section

namespace CFSG.KS.CentReg

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC

@[expose] noncomputable def sgnL (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => Nat.mul (nat_lit 2) (Nat.pred k))
    (fun k => Nat.succ (Nat.mul (nat_lit 2) k)) z

@[expose] noncomputable def wEval (L : Nat → Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.foldr (fun z y => L (sgnL z) y) x w

@[expose] noncomputable def wInvEval (L : Nat → Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.foldl (fun y z => L (Nat.xor (sgnL z) (nat_lit 1)) y) x w

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  foldN n (fun i s => Nat.add s (nIf(f i, nat_lit 1, nat_lit 0))) (nat_lit 0)

@[expose] noncomputable def fixCnt (n : Nat) (A : Nat → Nat) : Nat :=
  cntN n fun x => Nat.beq (A x) x

@[expose] noncomputable def hd (q : List Nat) : Nat := List.getD q (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def conjAt (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (A : Nat → Nat)
    (k z : Nat) : Nat :=
  hd (walkInvK L PAR LAB k (List.cons (A (hd (walkK L PAR LAB k (List.cons z List.nil)))) List.nil))

@[expose] noncomputable def centCnt (L : Nat → Nat → Nat) (PAR0 LAB0 PTS1 PAR1 LAB1 : Nat → Nat)
    (cnt1 : Nat) (A : Nat → Nat) (k b : Nat) : Nat :=
  strictN (conjAt L PAR0 LAB0 A k b) fun c =>
    cntN cnt1 fun j => Nat.beq (hd (walkK L PAR1 LAB1 j (List.cons c List.nil)))
      (conjAt L PAR0 LAB0 A k (r32 PTS1 j))

@[expose] noncomputable def centOK (L : Nat → Nat → Nat) (PTS0 PAR0 LAB0 : Nat → Nat) (cnt0 : Nat)
    (PTS1 PAR1 LAB1 : Nat → Nat) (cnt1 : Nat) (A : Nat → Nat) (k b m : Nat) : Bool :=
  bAnd(Nat.blt k cnt0, bAnd(Nat.beq (A (r32 PTS0 k)) (r32 PTS0 k),
    Nat.beq (centCnt L PAR0 LAB0 PTS1 PAR1 LAB1 cnt1 A k b) m))

@[expose] noncomputable def normK (L : Nat → Nat → Nat) (nk : Nat) (U : Nat → Nat → Nat) (nu : Nat)
    (UPOS : Nat → Nat) (ucnt n root : Nat) : Bool :=
  allN nk fun h => allN nu fun i =>
    strictB (L (Nat.mul (nat_lit 2) h) (U i (L (Nat.succ (Nat.mul (nat_lit 2) h)) root))) fun v =>
      bAnd(Nat.blt v n, Nat.blt (r32 UPOS v) ucnt)

@[expose] noncomputable def centUK (L : Nat → Nat → Nat) (PTS PAR LAB : Nat → Nat) (cnt : Nat)
    (U : Nat → Nat → Nat) (nu : Nat) (UPOS : Nat → Nat) (ucnt root : Nat) : Bool :=
  allN cnt fun j => strictB (r32 PTS j) fun y =>
    bIf(Nat.blt (r32 UPOS y) ucnt, true,
      bIf(allN nu fun i => Nat.beq (hd (walkK L PAR LAB j (List.cons (U i root) List.nil))) (U i y),
        false, true))

@[expose] noncomputable def conjW (G : Nat → Nat → Nat) (a0 : Nat) (w : List Int) (z : Nat) : Nat :=
  wEval G w (G a0 (wInvEval G w z))

@[expose] noncomputable def coverK (L : Nat → Nat → Nat) (PTS PAR LAB : Nat → Nat) (cnt : Nat)
    (G : Nat → Nat → Nat) (a0 : Nat) (W : Nat → List Int) (root b : Nat) : Bool :=
  allN cnt fun j => strictB (r32 PTS j) fun y =>
    (fun q => strictB (List.getD q (nat_lit 1) (nat_lit 0)) fun sy =>
      bIf(bAnd(Nat.blt (nat_lit 0) j, Nat.beq sy root),
        bAnd(Nat.beq (conjW G a0 (W j) root) y, Nat.beq (conjW G a0 (W j) b) (hd q)), true))
      (walkK L PAR LAB j (List.cons b (List.cons y List.nil)))

end CFSG.KS.CentReg

end
