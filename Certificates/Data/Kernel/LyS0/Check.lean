module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Const
public import Certificates.Data.Kernel.SporSch.LyMat
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KD.LyS0

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KS.SporSch.LyM

@[expose] noncomputable def mul (X Y : Nat) : Nat :=
  mulR 5 12 1332 111 8 CFSG.KD.OrdLy.L CFSG.KD.OrdLy.H CFSG.KD.OrdLy.CM CFSG.KD.OrdLy.RM X Y

@[expose] noncomputable def vld (X : Nat) : Bool :=
  validM 5 147852 CFSG.KD.OrdLy.L CFSG.KD.OrdLy.H X

@[expose] noncomputable def PP (T : Nat → Nat) (i : Nat) : Nat := Nat.land (T i) 4095

@[expose] noncomputable def PJ (T : Nat → Nat) (i : Nat) : Nat := Nat.shiftRight (T i) 12

@[expose] noncomputable def LT (T : Nat → Nat) (j i : Nat) : Nat :=
  T (Nat.add 2187 (Nat.add (Nat.mul 2187 j) i))

@[expose] noncomputable def DT (T : Nat → Nat) (i : Nat) : Nat := T (Nat.add 13122 i)

@[expose] noncomputable def SO (T : Nat → Nat) (i : Nat) : Nat := T (Nat.add 15309 i)

@[expose] noncomputable def SOI (T : Nat → Nat) (i : Nat) : Nat := T (Nat.add 17496 i)

@[expose] noncomputable def WT (T : Nat → Nat) (a k : Nat) : Nat :=
  T (Nat.add 19683 (Nat.add (Nat.mul 81 a) k))

@[expose] noncomputable def OP (T : Nat → Nat) (t : Nat) : Nat := T (Nat.add 196830 (Nat.mul 2 t))

@[expose] noncomputable def OQ (T : Nat → Nat) (t : Nat) : Nat :=
  T (Nat.add 196831 (Nat.mul 2 t))

@[expose] noncomputable def ek (G T : Nat → Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => CFSG.KD.OrdLy.ONE)
    (fun _ ih i => strictN (PP T i) (fun p => strictN (PJ T i) (fun j => mul (G j) (ih p))))

@[expose] noncomputable def E (G T : Nat → Nat) (i : Nat) : Nat :=
  strictN (DT T i) (fun d => ek G T d i)

@[expose] noncomputable def nth (l : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun k' _ => ih k') k) l k

@[expose] noncomputable def regs (A B : Nat) (T : Nat → Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat) [A, B]
    (fun t acc => acc ++ [mul (nth acc (OP T t)) (nth acc (OQ T t))])

@[expose] noncomputable def tmF (T : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ ih a b => nIf(Nat.blt (PP T a) a, LT T (PJ T a) (ih (PP T a) b), b))

@[expose] noncomputable def tm (T : Nat → Nat) (a b : Nat) : Nat := tmF T (Nat.succ a) a b

@[expose] noncomputable def leftK (G T : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i (fun i => allBlk 0 (fun j => strictB j (fun j =>
    strictB (LT T j i) (fun k =>
      bAnd(Nat.blt k 2187, Nat.beq (mul (G j) (E G T i)) (E G T k))))) 5)) len

@[expose] noncomputable def sortK (G T : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i (fun i => sortB (E G T) (SO T) (SOI T) 2187 i)) len

@[expose] noncomputable def witK (T : Nat → Nat) (a : Nat) : Bool :=
  allBlk 0 (fun k => strictB k (fun k => strictB (WT T a k) (fun c =>
    bAnd(Nat.blt c 2187, bAnd(bIf(Nat.beq k 0, true, Nat.blt (WT T a (Nat.sub k 1)) c),
      Nat.beq (tm T a c) (tm T c a)))))) 81

@[expose] noncomputable def killK (T : Nat → Nat) : Bool :=
  allN 2187 (fun a => strictB a (fun a => bIf(Nat.beq a 0, true,
    strictB (tm T a (tm T a a)) (fun c => bIf(Nat.beq c 0, witK T a, true)))))

@[expose] noncomputable def shapeK (T : Nat → Nat) : Bool :=
  bAnd(Nat.beq (T 0) 0, bAnd(Nat.beq (DT T 0) 0,
    allN 2187 (fun i => strictB i (fun i => bIf(Nat.beq i 0, true,
      bAnd(Nat.blt (PP T i) i, bAnd(Nat.blt (PJ T i) 5,
        Nat.beq (DT T i) (Nat.succ (DT T (PP T i))))))))))

@[expose] noncomputable def opsK (T : Nat → Nat) : Bool :=
  allN 745 (fun t => bAnd(Nat.blt (OP T t) (Nat.add t 2), Nat.blt (OQ T t) (Nat.add t 2)))

@[expose] def gensL : List Nat := [201, 362, 467, 637, 746]

@[expose] noncomputable def gensK (A B : Nat) (T G : Nat → Nat) : Bool :=
  strictB (nth (regs A B T 745) 0) (fun _ =>
    allBlk 0 (fun j => Nat.beq (nth (regs A B T 745) (nth gensL j)) (G j)) 5)

@[expose] noncomputable def listT (f : Nat → Nat) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun k n => Nat.beq k n)
    (fun x _ ih k n => bAnd(Nat.beq x (f k), ih (Nat.succ k) n))

@[expose] def nlSp (c : Char) : Char := if c = '\n' then ' ' else c

@[expose] def splitSp (c : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | x :: xs, acc => if x == c then acc.reverse :: splitSp c xs [] else splitSp c xs (x :: acc)

@[expose] def decL (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

@[expose] def natsL (cs : List Char) : List Nat :=
  ((splitSp ' ' (cs.map nlSp) []).filter fun l => !l.isEmpty).map decL

@[expose] def textOK (cs : List Char) : Bool :=
  cs.all fun c => c.isDigit || c == ' ' || c == '\n'

@[expose] noncomputable def parseOK (f : Nat → Nat) (cs : List Char) (n : Nat) : Bool :=
  textOK cs && listT f (natsL cs) 0 n

@[expose] noncomputable def parRec (T : Nat → Nat) (k : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod k 2) 0, PP T (Nat.div k 2), PJ T (Nat.div k 2))

@[expose] noncomputable def opsRec (T : Nat → Nat) (k : Nat) : Nat := T (Nat.add 196830 k)

@[expose] noncomputable def LRec (T : Nat → Nat) (k : Nat) : Nat := T (Nat.add 2187 k)

end CFSG.KD.LyS0

end
