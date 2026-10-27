module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Text

public section

namespace CFSG.KC.Misc.RuFourth

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Mathieu

@[expose] noncomputable def fmtGo (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun s => bIf(Nat.beq s 0, true, Nat.beq s 2))
    (fun ch _ ih s => strictB (Char.toNat ch) (fun c =>
      bIf(Nat.beq c 10, bIf(Nat.beq s 0, true, Nat.beq s 2),
      bIf(bAnd(Nat.ble 48 c, Nat.ble c 57), bIf(bAnd(Nat.beq s 1, Nat.beq c 48), false, ih 2),
      bIf(Nat.beq c 45, bIf(Nat.beq s 0, ih 1, bIf(Nat.beq s 3, ih 1, false)),
      bIf(Nat.beq c 32, bIf(Nat.beq s 2, ih 0, false), false)))))) cs

@[expose] noncomputable def wordsTextOK (cs : List Char) : Bool := fmtGo cs 3

@[expose] noncomputable def intsGo (cs : List Char) : Nat → Bool → Bool → List Int :=
  List.rec (motive := fun _ => Nat → Bool → Bool → List Int)
    (fun v neg st => Bool.rec (motive := fun _ => List Int) [] [Bool.rec (motive := fun _ => Int)
      (Int.ofNat v) (Int.negSucc (Nat.pred v)) neg] st)
    (fun ch _ ih v neg st =>
      strictL (Char.toNat ch) (fun c =>
      Bool.rec (motive := fun _ => List Int)
        (Bool.rec (motive := fun _ => List Int)
          (Bool.rec (motive := fun _ => List Int)
            (ih (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) neg true)
            (ih (nat_lit 0) true false) (Nat.beq c (nat_lit 45)))
          (Bool.rec (motive := fun _ => List Int) (ih (nat_lit 0) false false)
            (List.cons (Bool.rec (motive := fun _ => Int) (Int.ofNat v) (Int.negSucc (Nat.pred v)) neg)
              (ih (nat_lit 0) false false)) st)
          (Nat.beq c (nat_lit 32)))
        (Bool.rec (motive := fun _ => List Int) [] [Bool.rec (motive := fun _ => Int)
          (Int.ofNat v) (Int.negSucc (Nat.pred v)) neg] st)
        (Nat.beq c (nat_lit 10))))
    cs
where
  strictL (y : Nat) (k : Nat → List Int) : List Int :=
    Nat.rec (motive := fun _ => List Int) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def intsK (cs : List Char) : List Int := intsGo cs (nat_lit 0) false false

@[expose] noncomputable def letterP (R RI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    R (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    RI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def wordFrom (R RI : Nat → Nat) (wd : List Int) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) s
    (fun z _ ih => strictN ih (fun T => strictN (icode z) (fun c =>
      pcomp (nat_lit 16240) (nat_lit 14) (nat_lit 16383) (letterP R RI c) T))) wd

@[expose] noncomputable def ptWord (R RI : Nat → Nat) (wd : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => strictN (icode z) (fun c =>
      pg (nat_lit 14) (nat_lit 16383) (letterP R RI c) y))) wd x

@[expose] noncomputable def idP : Nat := pidn (nat_lit 16240) (nat_lit 14)

@[expose] noncomputable def fixCnt (P : Nat) : Nat :=
  foldN (nat_lit 16240) (fun i acc => nIf(Nat.beq (pg (nat_lit 14) (nat_lit 16383) P i) i,
    Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def letters3 (wd : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => strictB (icode z) (fun c =>
    bAnd(Nat.blt (nat_lit 1) c, bAnd(Nat.ble c (nat_lit 7), ih)))) wd

@[expose] noncomputable def zOK (R RI : Nat → Nat) (P0 : List Int) (y : Nat) : Bool :=
  bAnd(Nat.blt y (nat_lit 16240),
    bIf(Nat.beq (ptWord R RI P0 (ptWord R RI P0 y)) y, false, true))

@[expose] noncomputable def oneP (R RI : Nat → Nat) (P0 : List Int) (X k x : Nat) : Bool :=
  strictB (pcomp (nat_lit 16240) (nat_lit 14) (nat_lit 16383) X X) (fun x2 =>
  strictB (pcomp (nat_lit 16240) (nat_lit 14) (nat_lit 16383) x2 x2) (fun x4 =>
    bAnd(Nat.beq (pcomp (nat_lit 16240) (nat_lit 14) (nat_lit 16383) x4 x4) idP,
    bAnd(bIf(Nat.beq x4 idP, false, true),
    bAnd(Nat.blt x (nat_lit 16240),
    bAnd(bIf(Nat.beq (pg (nat_lit 14) (nat_lit 16383) x4 x) (ptWord R RI P0 (ptWord R RI P0 x)),
      false, true),
      Nat.beq (fixCnt x4) k))))))

end CFSG.KC.Misc.RuFourth

end
