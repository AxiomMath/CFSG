module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.SlpM

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def nthW (W : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun w _ ih j => Nat.rec (motive := fun _ => List Nat) w (fun i _ => ih i) j) W

@[expose] noncomputable def revApp (L acc : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun c _ ih acc => ih (List.cons c acc)) L acc

@[expose] noncomputable def look (E : List (Nat × Nat)) (n : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun p _ ih => nIf(Nat.beq p.1 n, p.2, ih)) E

@[expose] noncomputable def has (E : List (Nat × Nat)) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => orB (Nat.beq p.1 n) ih) E

@[expose] noncomputable def negC (inv : Bool) (c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))
    (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0)) inv

@[expose] noncomputable def nodeC (inv : Bool) (c : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 2) (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 3)))
    (nIf(negC inv c, nat_lit 1, nat_lit 0))

@[expose] noncomputable def letV (GA GB GB2 : Nat) (E : List (Nat × Nat)) (inv : Bool) (c : Nat) :
    Nat :=
  (fun a => nIf(Nat.beq a (nat_lit 0), GB2, nIf(Nat.beq a (nat_lit 1), GA,
    nIf(Nat.beq a (nat_lit 2), nIf(negC inv c, GB2, GB), look E (nodeC inv c)))))
    (Nat.shiftRight c (nat_lit 1))

@[expose] noncomputable def letOK (E : List (Nat × Nat)) (bnd : Bool) (j : Nat) (inv : Bool)
    (c : Nat) : Bool :=
  (fun a => orB (Nat.blt a (nat_lit 3))
    (andB (orB (notB bnd) (Nat.blt (Nat.sub a (nat_lit 3)) j)) (has E (nodeC inv c))))
    (Nat.shiftRight c (nat_lit 1))

@[expose] noncomputable def lettersOK (E : List (Nat × Nat)) (bnd : Bool) (j : Nat) (inv : Bool)
    (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (letOK E bnd j inv c) ih) cs

@[expose] noncomputable def prodV (mul : Nat → Nat → Nat) (ONE : Nat) (f : Nat → Nat)
    (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE
    (fun c cs' ih => List.rec (motive := fun _ => Nat) (f c) (fun _ _ _ => mul (f c) ih) cs') cs

@[expose] noncomputable def nodeLetters (W : List (List Nat)) (n : Nat) : List Nat :=
  (fun w => Bool.rec (motive := fun _ => List Nat) w (revApp w List.nil)
      (Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 1)))
    (nthW W (Nat.shiftRight n (nat_lit 1)))

@[expose] noncomputable def oddN (n : Nat) : Bool := Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def nodeOK (W : List (List Nat)) (E : List (Nat × Nat)) (n : Nat) : Bool :=
  lettersOK E true (Nat.shiftRight n (nat_lit 1)) (oddN n) (nodeLetters W n)

@[expose] noncomputable def nodeV (mul : Nat → Nat → Nat) (ONE GA GB GB2 : Nat)
    (W : List (List Nat)) (E : List (Nat × Nat)) (n : Nat) : Nat :=
  prodV mul ONE (letV GA GB GB2 E (oddN n)) (nodeLetters W n)

@[expose] noncomputable def outsOK (R : Nat → Nat) (E : List (Nat × Nat)) (outs : List (Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (andB (has E p.1) (Nat.beq (look E p.1) (R p.2))) ih) outs

@[expose] noncomputable def eqsOK (mul : Nat → Nat → Nat) (ONE GA GB GB2 : Nat)
    (E : List (Nat × Nat)) (eqs : List (List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (andB (andB (lettersOK E false 0 false e.1) (lettersOK E false 0 false e.2))
      (Nat.beq (prodV mul ONE (letV GA GB GB2 E false) e.1)
        (prodV mul ONE (letV GA GB GB2 E false) e.2))) ih) eqs

@[expose] noncomputable def neqsOK (mul : Nat → Nat → Nat) (ONE GA GB GB2 : Nat)
    (E : List (Nat × Nat)) (neqs : List (List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (andB (andB (lettersOK E false 0 false e.1) (lettersOK E false 0 false e.2))
      (notB (Nat.beq (prodV mul ONE (letV GA GB GB2 E false) e.1)
        (prodV mul ONE (letV GA GB GB2 E false) e.2)))) ih) neqs

@[expose] noncomputable def runNodes (mul : Nat → Nat → Nat) (ONE GA GB GB2 : Nat)
    (W : List (List Nat)) (fin : List (Nat × Nat) → Bool) (nodes : List Nat) :
    List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) fin
    (fun n _ ih E => andB (nodeOK W E n)
      (Nat.rec (motive := fun _ => Bool) (ih (List.cons (Prod.mk n (nat_lit 0)) E))
        (fun v _ => ih (List.cons (Prod.mk n (Nat.succ v)) E)) (nodeV mul ONE GA GB GB2 W E n)))
    nodes

@[expose] noncomputable def runIns (VLD : Nat → Bool) (R : Nat → Nat) (k : List (Nat × Nat) → Bool)
    (ins : List (Nat × Nat)) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) k
    (fun p _ ih E => andB (VLD (R p.2))
      (Nat.rec (motive := fun _ => Bool) (ih (List.cons (Prod.mk p.1 (nat_lit 0)) E))
        (fun v _ => ih (List.cons (Prod.mk p.1 (Nat.succ v)) E)) (R p.2)))
    ins

@[expose] noncomputable def chunkOK (mul : Nat → Nat → Nat) (ONE : Nat) (VLD : Nat → Bool)
    (GA GB GB2 : Nat) (W : List (List Nat)) (R : Nat → Nat) (ins : List (Nat × Nat))
    (nodes : List Nat) (outs : List (Nat × Nat)) (eqs neqs : List (List Nat × List Nat)) : Bool :=
  runIns VLD R (runNodes mul ONE GA GB GB2 W
    (fun E => andB (outsOK R E outs) (andB (eqsOK mul ONE GA GB GB2 E eqs)
      (neqsOK mul ONE GA GB GB2 E neqs))) nodes) ins List.nil

@[expose] noncomputable def nthL {α : Type} (d : α) (l : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun i _ => ih i) j) l

@[expose] noncomputable def appL (a b : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) b (fun w _ ih => List.cons w ih) a

end CFSG.KC.SlpM

end
