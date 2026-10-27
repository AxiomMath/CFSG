module

public import Certificates.Data.Kernel.U43Pk.Defs

public section

namespace CFSG.KD.L43Q8

open CFSG.KC.Enum CFSG.KD.U43Pk

@[expose] def ONEQ : Nat := 21267668214987600450844837656361172993

@[expose] def MONEQ : Nat := 42535336429975200901689675312722345986

@[expose] noncomputable def pkQ (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => strictN acc fun a => Nat.add a (Nat.shiftLeft (f k) (Nat.shiftLeft k 2))) 33

@[expose] def sum4 (f : Nat → Nat) : Nat := f 0 + f 1 + f 2 + f 3

@[expose] noncomputable def mulE (P Q k : Nat) : Nat :=
  if k < 16 then
    sum4 (fun l => dg P (4 * (k / 4) + l) *
      (if dg P 32 = 1 then dg Q (16 + (4 * l + k % 4)) else dg Q (4 * l + k % 4))) % 3
  else if k < 32 then
    sum4 (fun l => dg P (16 + (4 * ((k - 16) / 4) + l)) *
      (if dg P 32 = 1 then dg Q (4 * l + (k - 16) % 4)
        else dg Q (16 + (4 * l + (k - 16) % 4)))) % 3
  else (dg P 32 + dg Q 32) % 2

@[expose] noncomputable def mulQ (P Q : Nat) : Nat := pkQ (mulE P Q)

@[expose] noncomputable def invE (P k : Nat) : Nat :=
  if k < 16 then
    (if dg P 32 = 1 then dg P (4 * (k % 4) + k / 4) else dg P (16 + (4 * (k % 4) + k / 4)))
  else if k < 32 then
    (if dg P 32 = 1 then dg P (16 + (4 * ((k - 16) % 4) + (k - 16) / 4))
      else dg P (4 * ((k - 16) % 4) + (k - 16) / 4))
  else dg P 32

@[expose] noncomputable def invQ (P : Nat) : Nat := pkQ (invE P)

@[expose] noncomputable def eqQ (P Q : Nat) : Bool :=
  (dg P 32 == dg Q 32) &&
    ((List.range 16).all (fun k => dg P k % 3 == dg Q k % 3) ||
      (List.range 16).all (fun k => (dg P k + dg Q k) % 3 == 0))

@[expose] noncomputable def fnzQ (P : Nat) : Nat :=
  match (List.range 16).find? (fun k => dg P k % 3 != 0) with
  | some k => dg P k % 3
  | none => 0

@[expose] noncomputable def normQ (P : Nat) : Nat := if fnzQ P == 2 then mulQ MONEQ P else P

@[expose] noncomputable def actQ (G P : Nat) : Nat := strictN (mulQ G P) normQ

@[expose] def b3 (f : Nat → Nat) : Nat := (List.range 16).foldr (fun k acc => f k + 3 * acc) 0

@[expose] noncomputable def keyQ (P : Nat) : Nat :=
  2 * min (b3 fun k => dg P k % 3) (b3 fun k => (3 - dg P k % 3) % 3) + dg P 32 % 2

@[expose] noncomputable def validQ (P : Nat) : Bool :=
  (List.range 32).all (fun k => decide (dg P k < 3)) && decide (dg P 32 < 2) &&
    (List.range 4).all (fun i => (List.range 4).all (fun j =>
      sum4 (fun l => dg P (4 * i + l) * dg P (16 + (4 * j + l))) % 3 == (if i == j then 1 else 0)))

@[expose] noncomputable def memQ (X A B : Nat) : Bool :=
  eqQ X ONEQ || (eqQ X (mulQ A A) || (eqQ X A || (eqQ X (invQ A) || (eqQ X B ||
    (eqQ X (invQ B) || (eqQ X (mulQ A B) || (eqQ X (mulQ B A) || false)))))))

@[expose] noncomputable def commQ (X Y : Nat) : Bool := eqQ (mulQ X Y) (mulQ Y X)

@[expose] noncomputable def sameQ (A B QA QB : Nat) : Bool :=
  memQ A QA QB && memQ B QA QB && memQ QA A B && memQ QB A B

@[expose] noncomputable def conjQ (S X : Nat) : Nat := mulQ (mulQ S X) (invQ S)

@[expose] noncomputable def omegaQ (WC A B : Nat) : Bool :=
  strictB (conjQ WC A) fun CA => strictB (conjQ WC B) fun CB =>
  (!memQ CA A B || !memQ CB A B) &&
    (!commQ A CA || !commQ A CB || !commQ B CA || !commQ B CB)

@[expose] noncomputable def pairQ (Q1A Q1B Q2A Q2B WC A B : Nat) : Bool :=
  !eqQ (conjQ B A) (invQ A) || sameQ A B Q1A Q1B || sameQ A B Q2A Q2B || omegaQ WC A B

@[expose] noncomputable def posQ (n : Nat) (PA LA : Nat → Nat) (j : Nat) : Nat :=
  Nat.add (Nat.mul n (PA j)) (LA j)

@[expose] noncomputable def ptQ (n N : Nat) (G T : Nat → Nat) (E : Nat → Nat → Nat)
    (PA LA SO SOI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun P =>
  bAnd(validQ P, bAnd(CFSG.KS.SporSch.LyM.sortB (fun j => keyQ (T j)) SO SOI N i,
    bAnd(allBlk 0 (fun k => strictB (E i k) fun e =>
      bAnd(Nat.blt e N, bAnd(Nat.beq (actQ (G k) P) (T e),
        bIf(Nat.beq e 0, true, Nat.ble (posQ n PA LA e) (Nat.add (Nat.mul n i) k))))) n,
    bIf(Nat.beq i 0, bAnd(Nat.beq P ONEQ, bAnd(Nat.beq (PA 0) 0, Nat.beq (LA 0) 0)),
      bAnd(Nat.blt (PA i) i, bAnd(Nat.blt (LA i) n, bAnd(Nat.beq (E (PA i) (LA i)) i,
        bIf(Nat.beq (Nat.succ i) N, true,
          Nat.blt (posQ n PA LA i) (posQ n PA LA (Nat.succ i))))))))))

@[expose] noncomputable def blkQ (n N : Nat) (G T : Nat → Nat) (E : Nat → Nat → Nat)
    (PA LA SO SOI : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i fun i => ptQ n N G T E PA LA SO SOI i) len

end CFSG.KD.L43Q8

end
