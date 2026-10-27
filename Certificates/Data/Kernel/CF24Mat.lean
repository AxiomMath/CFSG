module

public import Certificates.Data.Kernel.McLMultK

public section

namespace CFSG.KC.CF24M

open CFSG.F3.Native CFSG.KS.F3L CFSG.KC.Enum CFSG.KC.McLMult

@[expose] noncomputable def abL4 (A Ai B Bi : V) (z : Int) : V :=
  Int.rec (motive := fun _ => V)
    (fun k => Bool.rec (motive := fun _ => V)
      (Bool.rec (motive := fun _ => V) Bi B (Nat.beq k (nat_lit 2))) A (Nat.beq k (nat_lit 1)))
    (fun k => Bool.rec (motive := fun _ => V) Bi Ai (Nat.beq k (nat_lit 0))) z

@[expose] noncomputable def abK4 (d E : Nat) (I A Ai B Bi : V) (w : List Int) : V :=
  List.rec (motive := fun _ => V) I (fun l _ ih => mulL d E (abL4 A Ai B Bi l) ih) w

@[expose] noncomputable def evalKn {m : Nat} (d E : Nat) (I : V) (X Xi : Nat → V)
    (w : List (Fin m × Bool)) : V :=
  List.rec (motive := fun _ => V) I
    (fun l _ ih => mulL d E (Bool.rec (motive := fun _ => V) (Xi l.1.val) (X l.1.val) l.2) ih) w

@[expose] noncomputable def allK {α : Type} (L : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def invPairK (d E : Nat) (I X Xi : V) : Bool :=
  bAnd(canonL d X, bAnd(canonL d Xi, bAnd(eqL (mulL d E X Xi) I, eqL (mulL d E Xi X) I)))

@[expose] noncomputable def neOneK (d : Nat) (I Z : V) : Bool :=
  bAnd(canonL d Z, Bool.not (eqL Z I))

@[expose] noncomputable def matCheckK {m : Nat} (d E : Nat) (I : V) (X Xi : Nat → V) (n : Nat)
    (rels : List (List (Fin m × Bool))) (r3 dd c : List (Fin m × Bool)) : Bool :=
  bAnd(allN n (fun i => invPairK d E I (X i) (Xi i)),
    bAnd(allK rels (fun w => eqL (evalKn d E I X Xi w) I),
      bAnd(eqL (evalKn d E I X Xi r3) I,
        bAnd(neOneK d I (evalKn d E I X Xi dd), neOneK d I (evalKn d E I X Xi c)))))

end CFSG.KC.CF24M

end
