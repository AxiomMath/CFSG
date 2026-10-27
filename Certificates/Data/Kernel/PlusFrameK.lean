module

public import Certificates.Data.Kernel.PlusQuandle
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.FrameCheck

public section

namespace CFSG.KC.PlusFrameK

open CFSG.KD.PlusQuandle

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => f k && ih) n

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k ih => f k || ih) n

@[expose] def rd (P q : Nat) : Nat := lane 6 P q

@[expose] def wr (P p v : Nat) : Nat := P ^^^ ((rd P p ^^^ v) <<< (6 * p))

@[expose] def isFr (p : Nat) : Bool := Nat.beq p 18 || Nat.beq p 31 || Nat.beq p 36 || Nat.beq p 41

@[expose] def initV (a b p : Nat) : Nat :=
  cond (isFr p) p (cond (Nat.beq p 0) a (cond (Nat.beq p 1) b 0))

@[expose] noncomputable def initK (a b n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p P => force P fun P => wr P p (initV a b p)) n

@[expose] def stepK (R : Nat → Nat) (a b P p s : Nat) : Nat :=
  wr P p (cond (Nat.beq s 0) (initV a b p) (tq R (rd P ((s - 1) / 60)) (rd P ((s - 1) % 60))))

@[expose] noncomputable def derK (R DS : Nat → Nat) (a b k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (initK a b 60)
    (fun j P => force P fun P => stepK R a b P (lane 12 (DS 0) j) (lane 12 (DS 1) j)) k

@[expose] noncomputable def homK (R : Nat → Nat) (P : Nat) : Bool :=
  allN 60 fun i => allN 60 fun j => Nat.beq (rd P (tq R i j)) (tq R (rd P i) (rd P j))

@[expose] noncomputable def matchK (DA : Nat → Nat) (P : Nat) : Bool :=
  anyN 8 fun k => allN 60 fun p => Nat.beq (rd P p) (rd (DA k) p)

@[expose] noncomputable def autK (R DS DA : Nat → Nat) (a : Nat) : Bool :=
  allN 60 fun b => force (derK R DS a b 60) fun P => !(homK R P) || matchK DA P

@[expose] noncomputable def autOK (R DS DA : Nat → Nat) (lo hi : Nat) : Bool :=
  allN (hi - lo) fun i => autK R DS DA (lo + i)

@[expose] def dsOK (DS : Nat → Nat) : Bool :=
  (List.range 60).map (lane 12 (DS 0)) == CFSG.OddTranspositions.PartThree.PlusFrame.derivOrder.toList &&
  (List.range 60).map (lane 12 (DS 1)) == CFSG.OddTranspositions.PartThree.PlusFrame.derivSrc.toList &&
  (List.range 60).all (fun k => Nat.blt (lane 12 (DS 0) k) 60 && Nat.ble (lane 12 (DS 1) k) 3600)

@[expose] def daOK (DA : Nat → Nat) : Bool :=
  (List.range 8).map (fun k => (List.range 60).map (rd (DA k))) ==
    (CFSG.OddTranspositions.PartThree.PlusFrame.dActions ()).map Array.toList

end CFSG.KC.PlusFrameK
