module

public import Certificates.Data.Kernel.Over77.Checks
public import CFSG.Certificates.Kernel.Common.StrSplit
public import CFSG.Certificates.Kernel.StrNlSp

public section

namespace CFSG.KC.Prim77

open CFSG.KC.Enum CFSG.KC.Over77

@[expose] noncomputable def idP : Nat := pidn (nat_lit 77) (nat_lit 7)

@[expose] noncomputable def im (p i : Nat) : Nat := pg (nat_lit 7) (nat_lit 127) p i

@[expose] noncomputable def wordK (g : Nat → Nat) (w : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun k _ ih acc => strictN (cp acc (g k)) ih) w acc

@[expose] noncomputable def powK (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun _ ih => strictN ih (fun v => cp v p)) k

@[expose] noncomputable def let5 (L0 L1 L2 L3 k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), L0, nIf(Nat.beq k (nat_lit 1), L1, nIf(Nat.beq k (nat_lit 2), L2,
    nIf(Nat.beq k (nat_lit 3), L3, idP))))

@[expose] noncomputable def letsB (A C : Nat) (f : Nat → Nat → Nat → Nat → Bool) : Bool :=
  strictB A (fun a => strictB C (fun c => strictB (powK a (nat_lit 2)) (fun a2 =>
    strictB (powK c (nat_lit 4)) (fun c4 => f a a2 c c4))))

@[expose] noncomputable def transW (g : Nat → Nat) (W : List (List Nat)) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 77))
    (fun w _ ih i => bAnd(Nat.beq (im (wordK g w idP) (nat_lit 0)) i, ih (Nat.succ i))) W i

@[expose] noncomputable def transK (g : Nat → Nat) (W : List (List Nat)) : Bool :=
  transW g W (nat_lit 0)

@[expose] noncomputable def lenK (R : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) R

@[expose] noncomputable def cnt0 (T : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add (nIf(Nat.beq x r, nat_lit 1, nat_lit 0)) ih) T

@[expose] noncomputable def cntK (R : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ T _ => cnt0 T r) R

@[expose] noncomputable def stabAt (g : Nat → Nat) (R : List Nat) (w : List Nat) (r i : Nat) :
    Bool :=
  strictB (wordK g w idP) (fun v => bAnd(Nat.beq (im v (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.blt r (nat_lit 77), bAnd(Nat.beq (im v r) i, Nat.ble (nat_lit 12) (cntK R r)))))

@[expose] noncomputable def stabW (g : Nat → Nat) (R : List Nat) (W : List (List Nat)) (i : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 77))
    (fun w _ ih i => bAnd(bIf(Nat.beq i (nat_lit 0), true, stabAt g R w (nth R i) i),
      ih (Nat.succ i))) W i

@[expose] noncomputable def stabK (g : Nat → Nat) (W : List (List Nat)) (R : List Nat) : Bool :=
  bAnd(Nat.beq (lenK R) (nat_lit 77), stabW g R W (nat_lit 0))

@[expose] noncomputable def neAny (p n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j ih => bIf(Nat.beq (im p j) j, ih, true)) n

@[expose] noncomputable def notIdK (p : Nat) : Bool := neAny p (nat_lit 77)

@[expose] noncomputable def ordK (p k : Nat) : Bool := bAnd(notIdK p, idK (powK p k))

@[expose] noncomputable def optB {α : Type} (o : Option α) (f : α → Bool) : Bool :=
  Option.rec (motive := fun _ => Bool) false f o

@[expose] def isNum (l : List Char) : Bool := !l.isEmpty && l.all Char.isDigit

@[expose] def numsK : List (List Char) → Option (List Nat)
  | [] => some []
  | p :: ps => if isNum p then (numsK ps).map (CFSG.KC.Str.decVal p :: ·) else none

@[expose] def numsL : List (List (List Char)) → Option (List (List Nat))
  | [] => some []
  | p :: ps => (numsK p).bind fun L => (numsL ps).map (L :: ·)

@[expose] def piecesW (cs : List Char) : List (List (List Char)) :=
  ((cs.splitOn '\n').filter fun l => [':'].isPrefixOf l).map fun l =>
    ((l.filter (· != ':')).splitOn ' ').filter fun t => !t.isEmpty

@[expose] def wordsO (cs : List Char) : Option (List (List Nat)) := numsL (piecesW cs)

@[expose] def natsO (cs : List Char) : Option (List Nat) :=
  numsK (((cs.map CFSG.KC.StrNlSp.nlSp).splitOn ' ').filter fun t => !t.isEmpty)

@[expose] noncomputable def arK (a : Nat) (d : Array Nat) : Bool :=
  bAnd(Nat.beq d.size (nat_lit 77), bAnd(canon a,
    allN (nat_lit 77) (fun i => Nat.beq (im a i) (d.getD i (nat_lit 0)))))

end CFSG.KC.Prim77

end
