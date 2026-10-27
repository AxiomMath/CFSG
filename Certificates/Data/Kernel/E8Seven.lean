module

public import Init

@[expose] public noncomputable section

namespace Certificates.E8Seven.K

def bA (a b : Bool) : Bool := Bool.rec false b a

def bI (a b : Bool) : Bool := Bool.rec true b a

def bN (a : Bool) : Bool := Bool.rec true false a

def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => bA (f k) acc) n

def hit (X c : Nat) : Nat :=
  Bool.rec 0 1 (Nat.beq (Nat.mod (Nat.mod (Nat.shiftRight (Nat.mul c X) 24) 256) 7) 0)

def cnt (X : Nat) (T : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ acc => Nat.add (hit X c) acc) T

def okMask : Nat := 4722366482870718955520

def ok (n : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight okMask n) 1) 1

def pack (a b c d : Nat) : Nat :=
  Nat.add a (Nat.add (Nat.mul 256 b) (Nat.add (Nat.mul 65536 c) (Nat.mul 16777216 d)))

def chk (T : List Nat) (a : Nat) : Bool :=
  allR 7 fun b => allR 7 fun c => allR 7 fun d =>
    bI (bN (Nat.beq (Nat.add a (Nat.add b (Nat.add c d))) 0)) (ok (cnt (pack a b c d) T))

end Certificates.E8Seven.K
