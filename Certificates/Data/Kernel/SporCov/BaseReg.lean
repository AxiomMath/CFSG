module

public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.SporCov.F2Reg
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.SporCov

open CFSG.KC.Loop

@[expose] noncomputable def imF (F : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (F c x) ih) w x

@[expose] noncomputable def gLB (fA fAi fB fBi : Nat → Nat) (Rg : List (List Nat)) (i : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (letB fA fAi fB fBi)
    (fun _ F c x => Bool.rec (motive := fun _ => Nat)
      (imF F (nthW Rg (Nat.sub c (nat_lit 4))) x) (letB fA fAi fB fBi c x)
      (Nat.blt c (nat_lit 4))) i

@[expose] noncomputable def glB (N : Nat) (lg : Nat → Nat) (s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (lg (Nat.sub s N)) s (Nat.blt s N)

@[expose] noncomputable def stB (N : Nat) (fA fAi fB fBi lg : Nat → Nat) (tb : Nat → Nat → Nat)
    (Rg : List (List Nat)) (n c s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Nat.add N (tb (Nat.sub c (nat_lit 4)) (Nat.sub s N)))
      (gLB fA fAi fB fBi Rg n c s) (Nat.blt s N))
    (letB fA fAi fB fBi c (glB N lg s)) (Nat.blt c (nat_lit 4))

@[expose] noncomputable def imBR (N : Nat) (fA fAi fB fBi lg : Nat → Nat) (tb : Nat → Nat → Nat)
    (Rg : List (List Nat)) (n : Nat) (w : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun c _ ih s => strictN (stB N fA fAi fB fBi lg tb Rg n c s) ih) w s

@[expose] noncomputable def keyBR (N : Nat) (fA fAi fB fBi lg : Nat → Nat) (tb : Nat → Nat → Nat)
    (Rg : List (List Nat)) (n : Nat) (bs : List Nat) (u : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.add (glB N lg (imBR N fA fAi fB fBi lg tb Rg n u (Nat.add N b)))
      (Nat.mul N ih)) bs

@[expose] noncomputable def eqBR (N : Nat) (fA fAi fB fBi lg : Nat → Nat) (tb : Nat → Nat → Nat)
    (Rg : List (List Nat)) (n : Nat) (bs : List Nat) (u v : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (glB N lg (imBR N fA fAi fB fBi lg tb Rg n u (Nat.add N b)))
      (glB N lg (imBR N fA fAi fB fBi lg tb Rg n v (Nat.add N b))), ih)) bs

@[expose] noncomputable def regB (N : Nat) (fA fAi fB fBi lg : Nat → Nat) (tb : Nat → Nat → Nat)
    (Rg : List (List Nat)) (n m i : Nat) : Bool :=
  chW (letRL i) (nthW Rg i) &&
    allLt m fun j => CFSG.KC.Enum.strictB (tb i j) fun t => bAnd(Nat.blt t m,
      Nat.beq (glB N lg (imBR N fA fAi fB fBi lg tb Rg n (nthW Rg i) (Nat.add N j))) (lg t))

@[expose] noncomputable def kitB (N : Nat) (fA fAi fB fBi lg : Nat → Nat) (tb : Nat → Nat → Nat)
    (Rg : List (List Nat)) (n m : Nat) (bs : List Nat)
    (k : (List Nat → List Nat → Bool) → (List Nat → Nat) → Bool) : Bool :=
  allLt m (fun j => Nat.blt (lg j) N) && chW (fun b => Nat.blt b m) bs &&
    allLt n (regB N fA fAi fB fBi lg tb Rg n m) &&
    k (eqBR N fA fAi fB fBi lg tb Rg n bs) (keyBR N fA fAi fB fBi lg tb Rg n bs)

end CFSG.KC.SporCov

end
