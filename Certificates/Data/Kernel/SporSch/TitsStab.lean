module

public import Certificates.Data.Kernel.SporSch.TitsInv

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu

@[expose] noncomputable def pgW (w p i : Nat) : Nat :=
  pg w (mask w) (Nat.land (Nat.shiftRight p (Nat.mul (Nat.mul (nat_lit 64) w)
    (Nat.div i (nat_lit 64)))) (mask (Nat.mul (nat_lit 64) w))) (Nat.mod i (nat_lit 64))

@[expose] noncomputable def permW (n w p q : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p (Nat.mul n w)) (nat_lit 0),
    bAnd(Nat.beq (Nat.shiftRight q (Nat.mul n w)) (nat_lit 0),
    allN n (fun i => strictB (pgW w p i) (fun v => bAnd(Nat.blt v n, Nat.beq (pgW w q v) i)))))

@[expose] noncomputable def eq2W (n w r p q : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p (Nat.mul n w)) (nat_lit 0),
    allN n (fun i => Nat.beq (pgW w r i) (pgW w p (pgW w q i))))

@[expose] noncomputable def wPtG (w : Nat) (S SI : Nat → Nat) (wd : List Int) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun z _ ih i => strictN (icode z) (fun c => strictN (ih i) (fun j =>
      pgW w (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) j))) wd i

@[expose] noncomputable def wordW (n w : Nat) (S SI : Nat → Nat) (kS : Nat) (wd : List Int)
    (r : Nat) : Bool :=
  bAnd(lettersK kS wd, allN n (fun p => Nat.beq (pgW w r p) (wPtG w S SI wd p)))

@[expose] noncomputable def strongK (n w : Nat) (PS PSI : Nat → Nat) :
    List (List Int) → Nat → Bool :=
  fun W => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun wd _ ih j => bAnd(wordW n w PS PSI j wd (PS j), ih (Nat.succ j))) W

@[expose] noncomputable def forest1K (n w : Nat) (GS : Nat → Nat) (kG r DEP PAR GL : Nat) :
    Bool :=
  bAnd(Nat.blt r n, bAnd(Nat.beq (pgW w DEP r) (nat_lit 0), allN n (fun x =>
    strictB (pgW w DEP x) (fun d => bIf(Nat.beq d (nat_lit 0), Nat.beq x r,
      strictB (pgW w PAR x) (fun p => bAnd(Nat.blt p n, bAnd(Nat.beq (Nat.succ (pgW w DEP p)) d,
        strictB (pgW w GL x) (fun g => bAnd(Nat.blt g kG, Nat.beq (pgW w (GS g) p) x))))))))))

@[expose] noncomputable def itN (g : Nat → Nat) (k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => g ih) k

@[expose] noncomputable def itRng (n : Nat) (g : Nat → Nat) (k p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(ih, Nat.blt (itN g j p) n)) k

@[expose] noncomputable def beqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (bIf(b, false, true)) b a

end CFSG.KS.SporSch

end
