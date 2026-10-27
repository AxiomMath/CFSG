module

public import Certificates.Data.Kernel.Spor.SlpMat

public section

namespace CFSG.KC.SlpM

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (f k)) n

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

@[expose] noncomputable def memP (q : Nat × Nat) (l : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => orB (andB (Nat.beq p.1 q.1) (Nat.beq p.2 q.2)) ih) l

@[expose] noncomputable def planOK (K nR base : Nat) (LY PC PN : Nat → Nat)
    (IN OU : Nat → List (Nat × Nat)) : Bool :=
  andB (allLt K fun k => allL (IN k) fun p =>
      andB (andB (Nat.blt 0 p.2) (Nat.blt p.2 nR)) (andB (Nat.beq (PN p.2) p.1)
        (andB (Nat.blt (PC p.2) k) (orB (Nat.beq (LY (PC p.2)) (LY k)) (Nat.blt p.1 base)))))
    (allLt nR fun r => orB (Nat.beq r 0) (andB (Nat.blt (PC r) K) (memP (PN r, r) (OU (PC r)))))

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def slpC (W : List (List Nat)) (j0 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih j => andB (allL w fun c => (fun a => andB (Nat.blt (nat_lit 0) a)
        (orB (Nat.ble a (nat_lit 2)) (Nat.blt a (Nat.add j (nat_lit 3))))) (Nat.shiftRight c (nat_lit 1)))
      (ih (Nat.succ j))) W j0

@[expose] noncomputable def eqLN (a b : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false (fun y ys _ => andB (Nat.beq x y) (ih ys)) b)
    a b

@[expose] noncomputable def memE (e : List Nat × List Nat) (l : List (List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => orB (andB (eqLN p.1 e.1) (eqLN p.2 e.2)) ih) l

@[expose] noncomputable def anyLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k ih => orB ih (f k)) n

@[expose] noncomputable def relC (x y : Nat) (v : List (Nat × Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun l _ ih => List.cons (Nat.add (Nat.mul (nat_lit 2)
      (Nat.add (nIf(Nat.beq l.1 (nat_lit 0), x, y)) (nat_lit 3))) (nIf(l.2, nat_lit 0, nat_lit 1))) ih) v

@[expose] noncomputable def memN (n : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun m _ ih => orB (Nat.beq m n) ih) l

@[expose] noncomputable def secC (W : List (List Nat)) (gs : List Nat) (lo hi : Nat) : Bool :=
  allLt (Nat.sub hi lo) fun r => allL (nthW W (Nat.add lo r)) fun c =>
    (fun a => andB (Nat.ble (nat_lit 3) a) (orB (memN (Nat.sub a (nat_lit 3)) gs)
      (andB (Nat.ble lo (Nat.sub a (nat_lit 3))) (Nat.blt (Nat.sub a (nat_lit 3)) (Nat.add lo r)))))
      (Nat.shiftRight c (nat_lit 1))

@[expose] noncomputable def hasEq (LY : Nat → Nat) (EQ : Nat → List (List Nat × List Nat)) (K l : Nat)
    (e : List Nat × List Nat) : Bool :=
  anyLt K fun k => andB (Nat.beq (LY k) l) (memE e (EQ k))

end CFSG.KC.SlpM

end
