module

public import Certificates.Data.Kernel.F4Syl3Model

public section

namespace CFSG.KC.F4Planes

open CFSG.KC.F4Syl3

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.rec false ih (f i)) n

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.rec false ih (f x)) l

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def bitB (M v : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 v))

@[expose] noncomputable def ent7 (T i : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 7 i)) 127

@[expose] noncomputable def ent4 (T i : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 4 i)) 15

@[expose] noncomputable def pmulT (VT AT QT m n : Nat) : Nat :=
  Nat.add (ent7 VT (Nat.add (Nat.mul 81 (Nat.mod m 81))
      (ent7 AT (Nat.add (Nat.mul 81 (Nat.div m 81)) (Nat.mod n 81)))))
    (Nat.mul 81 (ent4 QT (Nat.add (Nat.mul 9 (Nat.div m 81)) (Nat.div n 81))))

@[expose] noncomputable def tabChk (VT AT QT : Nat) : Bool :=
  allN 81 (fun a => allN 81 fun c => Nat.beq (ent7 VT (Nat.add (Nat.mul 81 a) c)) (vadd a c)) &&
  allN 9 (fun q => allN 81 fun a => Nat.beq (ent7 AT (Nat.add (Nat.mul 81 q) a)) (actQ q a)) &&
  allN 9 (fun q => allN 9 fun r => Nat.beq (ent4 QT (Nat.add (Nat.mul 9 q) r)) (qadd q r))

@[expose] noncomputable def omChk (VT AT QT OM : Nat) : Bool :=
  allN 729 fun v => Nat.beq v 0 || !Nat.beq (pmulT VT AT QT (pmulT VT AT QT v v) v) 0 || bitB OM v

@[expose] noncomputable def aR (PR r : Nat) : Nat := Nat.land (Nat.shiftRight PR (Nat.mul 20 r)) 1023

@[expose] noncomputable def bR (PR r : Nat) : Nat :=
  Nat.land (Nat.shiftRight PR (Nat.add (Nat.mul 20 r) 10)) 1023

@[expose] noncomputable def ord3B (VT AT QT m : Nat) : Bool :=
  Nat.blt m 729 && Nat.beq (pmulT VT AT QT (pmulT VT AT QT m m) m) 0

@[expose] noncomputable def repChk (VT AT QT PR : Nat) : Bool :=
  allN 67 fun r => ord3B VT AT QT (aR PR r) && ord3B VT AT QT (bR PR r) &&
    Nat.beq (pmulT VT AT QT (aR PR r) (bR PR r)) (pmulT VT AT QT (bR PR r) (aR PR r))

@[expose] noncomputable def planeL (VT AT QT a b : Nat) : List Nat :=
  [0, a, pmulT VT AT QT a a, b, pmulT VT AT QT a b, pmulT VT AT QT (pmulT VT AT QT a a) b,
    pmulT VT AT QT b b, pmulT VT AT QT a (pmulT VT AT QT b b),
    pmulT VT AT QT (pmulT VT AT QT a a) (pmulT VT AT QT b b)]

@[expose] noncomputable def conjT (VT AT QT y yi e : Nat) : Nat :=
  pmulT VT AT QT (pmulT VT AT QT y e) yi

@[expose] noncomputable def maskC (VT AT QT y yi : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => Nat.lor (Nat.shiftLeft 1 (conjT VT AT QT y yi e)) ih) l

@[expose] noncomputable def rowMask (VT AT QT PR : Nat) (row : Nat × Nat × Nat) : Nat :=
  maskC VT AT QT row.2.1 row.2.2 (planeL VT AT QT (aR PR row.1) (bR PR row.1))

@[expose] noncomputable def rowsMask (VT AT QT PR : Nat) (rows : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun row _ ih => Nat.lor (rowMask VT AT QT PR row) ih) rows

@[expose] noncomputable def rowB (VT AT QT PR u : Nat) (row : Nat × Nat × Nat) : Bool :=
  Nat.blt row.1 67 && Nat.blt row.2.1 729 && Nat.blt row.2.2 729 &&
    Nat.beq (pmulT VT AT QT row.2.1 row.2.2) 0 && bitB (rowMask VT AT QT PR row) u

@[expose] noncomputable def scanB (VT AT QT OM u u2 U : Nat) : Bool :=
  allN 729 fun v => !bitB OM v || !Nat.beq (pmulT VT AT QT u v) (pmulT VT AT QT v u) ||
    Nat.beq v u || Nat.beq v u2 || bitB U v

@[expose] noncomputable def rowsB (VT AT QT OM PR u : Nat) (rows : List (Nat × Nat × Nat)) : Bool :=
  Nat.blt u 729 && allL rows (rowB VT AT QT PR u) &&
    strictB (pmulT VT AT QT u u) fun u2 => strictB (rowsMask VT AT QT PR rows) fun U =>
      scanB VT AT QT OM u u2 U

@[expose] noncomputable def rowK (VT AT QT OM PR : Nat) (reps : List Nat)
    (rows : List (List (Nat × Nat × Nat))) (k : Nat) : Bool :=
  rowsB VT AT QT OM PR (reps.getD k 0) (rows.getD k [])

end CFSG.KC.F4Planes

end
