module

public import Init

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def ifB (c t e : Bool) : Bool := Bool.rec (motive := fun _ => Bool) e t c

@[expose] noncomputable def ifN (n t e : Nat) : Nat := Nat.rec (motive := fun _ => Nat) e (fun _ _ => t) n

@[expose] noncomputable def letB {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) L

@[expose] noncomputable def fA0 (p : Nat) : Nat := Nat.mod (Nat.div p 78125) 5
@[expose] noncomputable def fA1 (p : Nat) : Nat := Nat.mod (Nat.div p 15625) 5
@[expose] noncomputable def fA2 (p : Nat) : Nat := Nat.mod (Nat.div p 3125) 5
@[expose] noncomputable def fA3 (p : Nat) : Nat := Nat.mod (Nat.div p 625) 5
@[expose] noncomputable def fB0 (p : Nat) : Nat := Nat.mod (Nat.div p 125) 5
@[expose] noncomputable def fB1 (p : Nat) : Nat := Nat.mod (Nat.div p 25) 5
@[expose] noncomputable def fB2 (p : Nat) : Nat := Nat.mod (Nat.div p 5) 5
@[expose] noncomputable def fB3 (p : Nat) : Nat := Nat.mod p 5
@[expose] noncomputable def fS (p : Nat) : Nat := Nat.div p 390625

@[expose] noncomputable def cinv (d : Nat) : Nat := Nat.mod (Nat.mul d (Nat.mul d d)) 5

@[expose] noncomputable def nrm (r0 r1 r2 r3 r4 r5 r6 r7 s : Nat) : Nat :=
  letB (cinv (ifN (Nat.mod r0 5) r0 r1)) fun c =>
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r0) 5) 78125) <|
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r1) 5) 15625) <|
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r2) 5) 3125) <|
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r3) 5) 625) <|
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r4) 5) 125) <|
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r5) 5) 25) <|
    Nat.add (Nat.mul (Nat.mod (Nat.mul c r6) 5) 5) <|
    Nat.add (Nat.mod (Nat.mul c r7) 5) (Nat.mul s 390625)

@[expose] noncomputable def mul8 (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 s : Nat) : Nat :=
  nrm (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y2)) (Nat.add (Nat.mul x0 y1) (Nat.mul x1 y3))
    (Nat.add (Nat.mul x2 y0) (Nat.mul x3 y2)) (Nat.add (Nat.mul x2 y1) (Nat.mul x3 y3))
    (Nat.add (Nat.mul x4 y4) (Nat.mul x5 y6)) (Nat.add (Nat.mul x4 y5) (Nat.mul x5 y7))
    (Nat.add (Nat.mul x6 y4) (Nat.mul x7 y6)) (Nat.add (Nat.mul x6 y5) (Nat.mul x7 y7)) s

@[expose] noncomputable def mulK (p q : Nat) : Nat :=
  letB (fS p) fun s =>
  letB (fA0 p) fun x0 => letB (fA1 p) fun x1 => letB (fA2 p) fun x2 => letB (fA3 p) fun x3 =>
  letB (fB0 p) fun x4 => letB (fB1 p) fun x5 => letB (fB2 p) fun x6 => letB (fB3 p) fun x7 =>
  letB (fA0 q) fun y0 => letB (fA1 q) fun y1 => letB (fA2 q) fun y2 => letB (fA3 q) fun y3 =>
  letB (fB0 q) fun y4 => letB (fB1 q) fun y5 => letB (fB2 q) fun y6 => letB (fB3 q) fun y7 =>
  letB (Nat.mod (Nat.add s (fS q)) 2) fun t =>
    ifN s (mul8 x0 x1 x2 x3 x4 x5 x6 x7 y4 y5 y6 y7 y0 y1 y2 y3 t)
      (mul8 x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 t)

@[expose] noncomputable def inv8 (x0 x1 x2 x3 x4 x5 x6 x7 d e s : Nat) : Nat :=
  ifN s
    (nrm (Nat.mul e x7) (Nat.mul 4 (Nat.mul e x5)) (Nat.mul 4 (Nat.mul e x6)) (Nat.mul e x4)
      (Nat.mul d x3) (Nat.mul 4 (Nat.mul d x1)) (Nat.mul 4 (Nat.mul d x2)) (Nat.mul d x0) s)
    (nrm (Nat.mul d x3) (Nat.mul 4 (Nat.mul d x1)) (Nat.mul 4 (Nat.mul d x2)) (Nat.mul d x0)
      (Nat.mul e x7) (Nat.mul 4 (Nat.mul e x5)) (Nat.mul 4 (Nat.mul e x6)) (Nat.mul e x4) s)

@[expose] noncomputable def invK (p : Nat) : Nat :=
  letB (fS p) fun s =>
  letB (fA0 p) fun x0 => letB (fA1 p) fun x1 => letB (fA2 p) fun x2 => letB (fA3 p) fun x3 =>
  letB (fB0 p) fun x4 => letB (fB1 p) fun x5 => letB (fB2 p) fun x6 => letB (fB3 p) fun x7 =>
  letB (cinv (Nat.add (Nat.mul x0 x3) (Nat.mul 4 (Nat.mul x1 x2)))) fun d =>
  letB (cinv (Nat.add (Nat.mul x4 x7) (Nat.mul 4 (Nat.mul x5 x6)))) fun e =>
    inv8 x0 x1 x2 x3 x4 x5 x6 x7 d e s

@[expose] noncomputable def oneK : Nat := 78876

@[expose] noncomputable def validK (p : Nat) : Bool :=
  andB (Nat.blt p 781250) <|
  andB (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq (fA0 p) 0) (Nat.beq (fA1 p) 1)) true (Nat.beq (fA0 p) 1)) <|
  Nat.beq (Nat.mod (Nat.mul (Nat.add (Nat.mul (fA0 p) (fA3 p)) (Nat.mul 4 (Nat.mul (fA1 p) (fA2 p))))
      (Nat.add (Nat.mul (fB0 p) (fB3 p)) (Nat.mul 4 (Nat.mul (fB1 p) (fB2 p))))) 5) 1

@[expose] noncomputable def ordAuxK (x : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ k => k)
    (fun _ ih y k => Bool.rec (motive := fun _ => Nat) (ih (mulK y x) (Nat.succ k)) k (Nat.beq y oneK))
    fuel

@[expose] noncomputable def ordK (x : Nat) : Nat := ordAuxK x 300 x 1

end CFSG.KC.FiveStdK

end
