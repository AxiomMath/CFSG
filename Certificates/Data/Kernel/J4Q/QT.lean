module

public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop

@[expose] noncomputable def letOf (n : Nat) : Int :=
  Bool.rec (motive := fun _ => Int)
    (Bool.rec (motive := fun _ => Int)
      (Bool.rec (motive := fun _ => Int)
        (Bool.rec (motive := fun _ => Int)
          (Bool.rec (motive := fun _ => Int)
            (Bool.rec (motive := fun _ => Int) (Int.ofNat (nat_lit 0)) (Int.negSucc (nat_lit 2))
              (Nat.beq n (nat_lit 67)))
            (Int.negSucc (nat_lit 1)) (Nat.beq n (nat_lit 66)))
          (Int.negSucc (nat_lit 0)) (Nat.beq n (nat_lit 65)))
        (Int.ofNat (nat_lit 3)) (Nat.beq n (nat_lit 99)))
      (Int.ofNat (nat_lit 2)) (Nat.beq n (nat_lit 98)))
    (Int.ofNat (nat_lit 1)) (Nat.beq n (nat_lit 97))

@[expose] noncomputable def isLet (n : Nat) : Bool :=
  orB (Nat.beq n (nat_lit 97)) (orB (Nat.beq n (nat_lit 98)) (orB (Nat.beq n (nat_lit 99))
    (orB (Nat.beq n (nat_lit 65)) (orB (Nat.beq n (nat_lit 66)) (Nat.beq n (nat_lit 67))))))

@[expose] noncomputable def lettersK (cs : List Char) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil
    (fun ch _ ih => Bool.rec (motive := fun _ => List Int) ih (List.cons (letOf (Char.toNat ch)) ih)
      (isLet (Char.toNat ch))) cs

@[expose] noncomputable def negRevOnto (w : List Int) : List Int → List Int :=
  List.rec (motive := fun _ => List Int → List Int) (fun acc => acc)
    (fun l _ ih acc => ih (List.cons (Int.neg l) acc)) w

@[expose] noncomputable def negRev (w : List Int) : List Int := negRevOnto w List.nil

@[expose] noncomputable def allNeK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (neN x y) ih) l

@[expose] noncomputable def distinctK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => andB (allNeK x xs) ih) l

@[expose] noncomputable def w5K (cs : List Char) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil
    (fun ch _ ih => (fun k => Bool.rec (motive := fun _ => List Int)
      (Bool.rec (motive := fun _ => List Int) ih
        (List.cons (Int.negSucc (Nat.sub k (nat_lit 65))) ih)
        (andB (Nat.ble (nat_lit 65) k) (Nat.ble k (nat_lit 69))))
      (List.cons (Int.ofNat (Nat.sub k (nat_lit 96))) ih)
      (andB (Nat.ble (nat_lit 97) k) (Nat.ble k (nat_lit 101)))) (Char.toNat ch)) cs

@[expose] noncomputable def revOnto {α : Type} (l : List α) : List α → List α :=
  List.rec (motive := fun _ => List α → List α) (fun out => out) (fun x _ ih out => ih (List.cons x out)) l

@[expose] noncomputable def strictL {α : Type} (y : Nat) (k : Nat → List α) : List α :=
  Nat.rec (motive := fun _ => List α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def smapRev (f : Nat → Nat) (l : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => strictL (f x) fun v => ih (List.cons v acc)) l

@[expose] noncomputable def smapK (f : Nat → Nat) (l : List Nat) : List Nat :=
  revOnto (smapRev f l List.nil) List.nil

@[expose] noncomputable def rangeK (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons k acc)) n List.nil

@[expose] noncomputable def isDig (n : Nat) : Bool := andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57))

@[expose] noncomputable def ptsGo (cs : List Char) :
    Bool → Nat → Bool → List Int → List (Nat × List Int) :=
  List.rec (motive := fun _ => Bool → Nat → Bool → List Int → List (Nat × List Int))
    (fun _ n ne acc => Bool.rec (motive := fun _ => List (Nat × List Int)) List.nil
      (List.cons (Prod.mk n (revOnto acc List.nil)) List.nil) ne)
    (fun ch _ ih d n ne acc => (fun k => Bool.rec (motive := fun _ => List (Nat × List Int))
      (Bool.rec (motive := fun _ => List (Nat × List Int))
        (ih false n true (Bool.rec (motive := fun _ => List Int) acc (List.cons (letOf k) acc) (isLet k)))
        (ih true (Nat.add (Nat.mul n (nat_lit 10)) (Nat.sub k (nat_lit 48))) true acc)
        (andB d (isDig k)))
      (Bool.rec (motive := fun _ => List (Nat × List Int)) (ih true (nat_lit 0) false List.nil)
        (List.cons (Prod.mk n (revOnto acc List.nil)) (ih true (nat_lit 0) false List.nil)) ne)
      (Nat.beq k (nat_lit 32))) (Char.toNat ch))
    cs

@[expose] noncomputable def ptsK (cs : List Char) : List (Nat × List Int) :=
  ptsGo cs true (nat_lit 0) false List.nil

@[expose] noncomputable def idxGo (cs : List Char) : Nat → Bool → List Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → Bool → List Nat → List (List Nat))
    (fun m u acc => Bool.rec (motive := fun _ => List (List Nat))
      (List.cons (Bool.rec (motive := fun _ => List Nat) (revOnto acc List.nil) List.nil u) List.nil)
      List.nil (Nat.beq m (nat_lit 0)))
    (fun ch _ ih m u acc => (fun k => Bool.rec (motive := fun _ => List (List Nat))
      (ih (Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 1) (Nat.beq m (nat_lit 0)))
        (andB (Nat.beq m (nat_lit 0)) (Nat.beq k (nat_lit 95)))
        (List.cons (Nat.sub k (nat_lit 97)) acc))
      (Bool.rec (motive := fun _ => List (List Nat))
        (List.cons (Bool.rec (motive := fun _ => List Nat) (revOnto acc List.nil) List.nil u)
          (ih (nat_lit 0) false List.nil))
        (ih (nat_lit 0) false List.nil) (Nat.beq m (nat_lit 0)))
      (Nat.beq k (nat_lit 32))) (Char.toNat ch))
    cs

@[expose] noncomputable def idxK (cs : List Char) : List (List Nat) :=
  idxGo cs (nat_lit 0) false List.nil

@[expose] noncomputable def bitB (m j : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m j) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def selPK (c rm : Nat) (P : List (Nat × Nat)) (m : Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => Prod.rec (motive := fun _ => Nat)
      (fun j M => Bool.rec (motive := fun _ => Nat) (ih acc) (strictN (mulJ c rm acc M) ih) (bitB m j)) p)
    P

@[expose] noncomputable def etaFrom (c rm : Nat) (Ts : List Nat) (m : Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun T _ ih j acc => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j) acc)
      (strictN (mulJ c rm acc T) (ih (Nat.succ j)))
      (Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j)))) Ts

@[expose] noncomputable def etaK (c rm one : Nat) (Ts : List Nat) (m : Nat) : Nat :=
  etaFrom c rm Ts m (nat_lit 0) one

end CFSG.KC.J4Q

end
