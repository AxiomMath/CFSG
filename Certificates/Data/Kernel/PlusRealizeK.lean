module

public section

namespace CFSG.KC.PlusRealizeK

@[expose] def VSof (A : Array (Array Nat)) : List (List Nat) := A.toList.map Array.toList

@[expose] def on4 (f : Nat → Nat → Nat → Nat → Bool) : List Nat → Bool
  | [a, b, c, d] => f a b c d
  | _ => false

@[expose] noncomputable def allL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => p x && ih) L

@[expose] noncomputable def anyL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => p x || ih) L

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => f k && ih) n

@[expose] noncomputable def pw {α : Type} (R : α → α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => allL (R x) xs && ih) L

@[expose] noncomputable def getL (t : Nat) (L : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih t => Nat.rec (motive := fun _ => List Nat) x (fun k _ => ih k) t) L t

@[expose] def qN (a b c d : Nat) : Nat := (a * a + b * b + c * c + 4 * (d * d)) % 5

@[expose] def bN (a b c d e f g h : Nat) : Nat := (a * e + b * f + c * g + 4 * (d * h)) % 5

@[expose] def leadN (a b c d : Nat) : Nat :=
  cond (Nat.beq a 0) (cond (Nat.beq b 0) (cond (Nat.beq c 0) d c) b) a

@[expose] def invN (x : Nat) : Nat := x * x * x % 5

@[expose] def eqN4 (x : List Nat) (a b c d : Nat) : Bool :=
  on4 (fun p q r s => Nat.beq p a && Nat.beq q b && Nat.beq r c && Nat.beq s d) x

@[expose] def eqS (x : List Nat) (i a b c d : Nat) : Bool :=
  eqN4 x (a * i % 5) (b * i % 5) (c * i % 5) (d * i % 5)

@[expose] def normEq (x : List Nat) (a b c d : Nat) : Bool :=
  Nat.blt 0 (leadN a b c d) && eqS x (invN (leadN a b c d)) a b c d

@[expose] def signB (π : Bool) (q : Nat) : Bool :=
  cond π (Nat.beq q 1 || Nat.beq q 4) (Nat.beq q 2 || Nat.beq q 3)

@[expose] noncomputable def signOK (π : Bool) (L : List (List Nat)) : Bool :=
  allL (on4 fun a b c d => signB π (qN a b c d)) L

@[expose] noncomputable def tabW (L : List (List Nat)) (t q b a0 a1 a2 a3 e f g h : Nat) : Bool :=
  normEq (getL t L) ((q * e + 3 * b * a0) % 5) ((q * f + 3 * b * a1) % 5)
    ((q * g + 3 * b * a2) % 5) ((q * h + 3 * b * a3) % 5)

@[expose] noncomputable def tabE (L : List (List Nat)) (u v : List Nat) (t : Nat) : Bool :=
  on4 (fun a b c d => on4 (fun e f g h =>
    tabW L t (qN a b c d) (bN e f g h a b c d) a b c d e f g h) v) u

@[expose] noncomputable def tabOK (L T : List (List Nat)) : Bool :=
  allL (fun p : List Nat × List Nat =>
    allL (fun q : List Nat × Nat => tabE L p.1 q.1 q.2) (List.zip L p.2)) (List.zip L T)

@[expose] def propM (x y : List Nat) (m : Nat) : Bool :=
  on4 (fun a b c d => on4 (fun e f g h => eqS [a % 5, b % 5, c % 5, d % 5] m e f g h) y) x

@[expose] noncomputable def notProp (x y : List Nat) : Bool :=
  allN 5 fun m => !(propM x y m) && !(propM y x m)

@[expose] noncomputable def distOK (L : List (List Nat)) : Bool := pw notProp L

@[expose] noncomputable def covE (π : Bool) (L : List (List Nat)) (a b c d : Nat) : Bool :=
  !(Nat.blt 0 (qN a b c d) && signB π (qN a b c d)) || anyL (fun x => normEq x a b c d) L

@[expose] noncomputable def covOK (π : Bool) (L : List (List Nat)) : Bool :=
  allN 5 fun a => allN 5 fun b => allN 5 fun c => allN 5 fun d => covE π L a b c d

end CFSG.KC.PlusRealizeK
