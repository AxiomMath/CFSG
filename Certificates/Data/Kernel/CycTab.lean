module

public section

namespace CFSG.KC.CycTab

@[expose] noncomputable def fgK (T f : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul f (nat_lit 8))) (nat_lit 255)

@[expose] noncomputable def allLtK (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.rec false ih (p i)) n

@[expose] noncomputable def swapK (a b x : Nat) : Nat :=
  Bool.rec (Bool.rec x a (Nat.beq x b)) b (Nat.beq x a)

@[expose] noncomputable def cycGoK (n x : Nat) (a : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => x)
    (fun b _ ih a => swapK (Nat.mod a n) (Nat.mod b n) (ih b)) l a

@[expose] noncomputable def cycK (n : Nat) (c : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun a l _ => cycGoK n x a l) c

@[expose] noncomputable def cycsK (n : Nat) (cs : List (List Nat)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => cycK n c ih) cs

@[expose] noncomputable def genOK (n : Nat) (cs : List (List Nat)) (TT i : Nat) : Bool :=
  allLtK n fun x =>
    Bool.rec false
      (Bool.rec false
        (Nat.beq (fgK TT (Nat.add (Nat.mul (Nat.mul (nat_lit 2) i) n)
          (fgK TT (Nat.add (Nat.mul (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)) n) x)))) x)
        (Nat.blt (fgK TT (Nat.add (Nat.mul (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)) n) x)) n))
      (Nat.beq (fgK TT (Nat.add (Nat.mul (Nat.mul (nat_lit 2) i) n) x)) (cycsK n cs x))

@[expose] noncomputable def gensGoK (n : Nat) (CS : List (List (List Nat))) (TT : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun cs _ ih i => Bool.rec false (ih (Nat.succ i)) (genOK n cs TT i)) CS

@[expose] noncomputable def gensOK (n : Nat) (CS : List (List (List Nat))) (TT : Nat) : Bool :=
  gensGoK n CS TT (nat_lit 0)

@[expose] noncomputable def wordK (n TT : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun k _ ih => fgK TT (Nat.add (Nat.mul k n) ih)) w

@[expose] noncomputable def sqOK (n TT : Nat) (w : List Nat) : Bool :=
  allLtK n fun x => Nat.beq (wordK n TT w (wordK n TT w x)) x

@[expose] noncomputable def relsOK (n TT : Nat) (RS : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => Bool.rec false ih (sqOK n TT w)) RS

end CFSG.KC.CycTab

end
