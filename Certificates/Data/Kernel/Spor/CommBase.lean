module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.CommBase

open CFSG.KC.Enum

abbrev BaseRec : Type := Nat × List (List Nat) × List (Nat × Nat) × List (Nat × List Nat) × Nat

@[expose] noncomputable def notB (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) l

@[expose] noncomputable def anyL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(f a, true, ih)) l

@[expose] noncomputable def wapp (w m : Nat) (L : Nat → Nat) (W : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun z _ ih => strictN ih (fun v => pg w m (L z) v)) W

@[expose] noncomputable def lettersOK (nL : Nat) (W : List Nat) : Bool :=
  allL (fun z => Nat.blt z nL) W

@[expose] noncomputable def fixAll (w m : Nat) (L : Nat → Nat) (ss : List (List Nat)) (y : Nat) :
    Bool :=
  allL (fun s => Nat.beq (wapp w m L s y) y) ss

@[expose] noncomputable def allowed (b : Nat) (ex : List (Nat × Nat)) (sw : List (Nat × List Nat))
    (pr y : Nat) : Bool :=
  bIf(Nat.beq y b, true, bIf(Nat.beq pr b,
    bIf(anyL (fun e => Nat.beq e.1 y) ex, true, anyL (fun t => Nat.beq t.1 y) sw),
    Nat.beq y pr))

@[expose] noncomputable def baseOKc (n w m : Nat) (L : Nat → Nat) (nL b : Nat)
    (ss : List (List Nat)) (ex : List (Nat × Nat)) (sw : List (Nat × List Nat)) (pr : Nat) : Bool :=
  bAnd(Nat.blt b n, bAnd(Nat.blt pr n,
  bAnd(allL (lettersOK nL) ss,
  bAnd(allL (fun s => Nat.beq (wapp w m L s b) b) ss,
  bAnd(allL (fun e => bAnd(Nat.blt e.2 nL, bAnd(notB (Nat.beq (pg w m (L e.2) b) b),
      Nat.beq (pg w m (L e.2) e.1) e.1))) ex,
  bAnd(allL (fun t => bAnd(lettersOK nL t.2, bAnd(Nat.beq (wapp w m L t.2 b) t.1,
      Nat.beq (wapp w m L t.2 t.1) b))) sw,
  allN n (fun y => bIf(fixAll w m L ss y, allowed b ex sw pr y, true))))))))

@[expose] noncomputable def baseOK (n w m : Nat) (L : Nat → Nat) (nL : Nat) (r : BaseRec) : Bool :=
  baseOKc n w m L nL r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2

@[expose] noncomputable def forestOK (n w m : Nat) (L : Nat → Nat) (nL : Nat) (B : List BaseRec)
    (PF ZF DF : Nat) : Bool :=
  allN n (fun p => strictB (pg w m PF p) (fun q =>
    bIf(Nat.beq q p, anyL (fun r => Nat.beq r.1 p) B,
      bAnd(Nat.blt q n, strictB (pg w m ZF p) (fun z => bAnd(Nat.blt z nL,
        bAnd(Nat.blt (pg w m DF q) (pg w m DF p), Nat.beq (pg w m (L z) q) p)))))))

@[expose] noncomputable def commBaseOK (n w m : Nat) (L : Nat → Nat) (nL : Nat) (B : List BaseRec)
    (PF ZF DF : Nat) : Bool :=
  bAnd(allL (baseOK n w m L nL) B, forestOK n w m L nL B PF ZF DF)

end CFSG.KC.CommBase

end
