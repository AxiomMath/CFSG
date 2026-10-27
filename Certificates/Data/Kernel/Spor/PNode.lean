module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PNode

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def pathK (PL : Nat → Nat) (fuel : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih i => Bool.rec (motive := fun _ => List Nat)
      (List.cons (labOf PL i) (ih (parOf PL i))) List.nil (Nat.beq i (nat_lit 0))) fuel

@[expose] noncomputable def getK (l : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun k _ => ih k) i) l j

@[expose] noncomputable def memK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) l

@[expose] noncomputable def parK (PP : List Nat) (p : List Nat) : Nat :=
  Nat.mod (List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j _ ih => Nat.add (getK PP j) ih) p) (nat_lit 2)

@[expose] noncomputable def pathCodes (PL : Nat → Nat) (PR : List Nat) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun j _ ih => List.cons (Nat.succ (Nat.mul (nat_lit 2) (getK PR j))) ih) (pathK PL i i)

@[expose] noncomputable def nodeK (n w m : Nat) (T PL : Nat → Nat) (PP INV : List Nat)
    (i nw : Nat) : Bool :=
  bIf(Nat.beq (parK PP (pathK PL i i)) (nat_lit 1),
    bIf(Nat.beq nw (nat_lit 0), memK i INV,
      strictB (Nat.sub nw (nat_lit 1)) (fun x => strictB (T i) (fun t =>
        bAnd(Nat.blt x n, bIf(Nat.beq (pg w m t (pg w m t x)) x, false, true))))),
    bAnd(Nat.beq nw (nat_lit 0), bIf(memK i INV, false, true)))

@[expose] noncomputable def nodesK (n w m : Nat) (T PL : Nat → Nat) (PP INV : List Nat)
    (NW : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun nw _ ih i => bAnd(nodeK n w m T PL PP INV i nw, ih (Nat.succ i))) NW

@[expose] noncomputable def eqLK (u : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun v => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v)
    (fun x _ ih v => List.rec (motive := fun _ => Bool) false
      (fun y v' _ => bAnd(Nat.beq x y, ih v')) v) u

@[expose] noncomputable def sqPathsK (PL : Nat → Nat) (PR : List Nat) (INV : List Nat) :
    List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun R => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) R)
    (fun i _ ih R => List.rec (motive := fun _ => Bool) false
      (fun r R' _ => bAnd(eqLK r (List.append (pathCodes PL PR i) (pathCodes PL PR i)), ih R')) R)
    INV

end CFSG.KS.PNode

end
