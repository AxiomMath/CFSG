module

public import Certificates.Data.Kernel.HNF26729K

public section

namespace CFSG.KC.HN3

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KC.HNF26720 CFSG.KC.HNF26729

@[expose] noncomputable def headN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def tailN (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) l

@[expose] noncomputable def getL (l : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def setN (l : List Nat) (i x : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun m t ih i => Nat.rec (motive := fun _ => List Nat) (List.cons x t)
      (fun j _ => List.cons m (ih j)) i) l i

@[expose] noncomputable def forceLB (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun x _ ih k => strictB x fun a => ih fun t => k (List.cons a t)) l k

@[expose] noncomputable def regM (R : List Nat) (r : Nat) : Nat := getN 0 R (Nat.mul 2 r)

@[expose] noncomputable def regI (R : List Nat) (r : Nat) : Nat :=
  getN 0 R (Nat.add (Nat.mul 2 r) 1)

@[expose] noncomputable def setR (R : List Nat) (k x y : Nat) : List Nat :=
  setN (setN R (Nat.mul 2 k) x) (Nat.add (Nat.mul 2 k) 1) y

@[expose] noncomputable def stepM (mul : Nat → Nat → Nat) (R : List Nat) (code : List Nat) :
    List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (setR R (getN 0 code 2) (regI R (getN 0 code 1)) (regM R (getN 0 code 1)))
    (setR R (getN 0 code 3) (mul (regM R (getN 0 code 1)) (regM R (getN 0 code 2)))
      (mul (regI R (getN 0 code 2)) (regI R (getN 0 code 1))))
    (Nat.beq (getN 0 code 0) 0)

@[expose] noncomputable def runM (mul : Nat → Nat → Nat) (P : List (List Nat)) :
    List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun R k => k R)
    (fun code _ ih R k => forceLB (stepM mul R code) fun R' => ih R' k) P

@[expose] def initM (ONE A B Bi : Nat) : List Nat :=
  ONE :: ONE :: A :: A :: B :: Bi :: List.replicate 22 ONE

@[expose] noncomputable def progK (mul : Nat → Nat → Nat) (A B ONE : Nat) (P : List (List Nat))
    (regs : List Nat) : Bool :=
  strictB (mul B B) fun Bi =>
  andB (Nat.beq (mul A A) ONE) (andB (Nat.beq (mul B Bi) ONE)
    (runM mul P (initM ONE A B Bi) fun R =>
      andB (Nat.beq (getN 0 R 22) (getN 0 regs 0)) (andB (Nat.beq (getN 0 R 23) (getN 0 regs 1))
      (andB (Nat.beq (getN 0 R 24) (getN 0 regs 2)) (andB (Nat.beq (getN 0 R 25) (getN 0 regs 3))
      (andB (Nat.beq (getN 0 R 26) (getN 0 regs 4)) (Nat.beq (getN 0 R 27) (getN 0 regs 5))))))))

@[expose] noncomputable def wordG (mul : Nat → Nat → Nat) (G : List Nat) (w : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (mul acc (getN 0 G c)) ih) w

@[expose] noncomputable def relsK (mul : Nat → Nat → Nat) (G : List Nat) (ONE : Nat)
    (rels : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (wordG mul G r ONE) ONE) ih) rels

@[expose] noncomputable def rowK (vec : Nat → Nat → Nat) (S : List Nat) (x : Nat)
    (gens : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun g _ ih js => andB (Nat.beq (vec x g) (getN (headN S) S (headN js))) (ih (tailN js)))
    gens

@[expose] noncomputable def closeK (vec : Nat → Nat → Nat) (S : List Nat) (gens : List Nat)
    (xs : List Nat) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun x _ ih I => andB (rowK vec S x gens (List.rec (motive := fun _ => List Nat) List.nil
      (fun r _ _ => r) I)) (ih (List.rec (motive := fun _ => List (List Nat)) List.nil
      (fun _ t _ => t) I))) xs

@[expose] noncomputable def treeK (I : List (List Nat)) (ng : Nat) (T : List (Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih k => andB (Nat.blt e.1 k) (andB (Nat.blt e.2 ng)
      (andB (Nat.beq (getN 0 (getL I e.1) e.2) k) (ih (Nat.succ k))))) T

@[expose] noncomputable def orbK (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool) (G : List Nat)
    (ONE : Nat) (gw : List (List Nat)) (S : List Nat) (I : List (List Nat))
    (T : List (Nat × Nat)) (O : List Nat) (n : Nat) : Bool :=
  forceLB (gw.map fun w => wordG mul G w ONE) fun gens =>
    andB (vldV (headN S)) (andB (Nat.beq S.length n) (andB (Nat.beq (Nat.succ T.length) n)
      (andB (Nat.beq O.length n) (andB (closeK vec S gens S I)
        (andB (treeK I gens.length T 1) (incrK (headN S) S O 0))))))

end CFSG.KC.HN3

end
