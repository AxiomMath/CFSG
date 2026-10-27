module

public import Init

public section

namespace CFSG.KC.HMathieu

@[expose] def subX : List Nat → List Nat
  | [] => [0]
  | y :: l => subX l ++ (subX l).map (y ^^^ ·)

@[expose] def startX (R : List Nat) : List Nat → Nat
  | [] => 0
  | a :: _ => R.idxOf a + 1

@[expose] def gExtX (R l : List Nat) : List Nat :=
  (R.drop (startX R l)).filter fun x =>
    !((subX l).contains x) && (subX l).all fun s => s == 0 || decide (R.idxOf x < R.idxOf (x ^^^ s))

@[expose] def fGX (R : List Nat) (pred : List Nat → Bool) : Nat → List Nat → Bool
  | 0, l => pred l
  | k + 1, l => (gExtX R l).all fun x => fGX R pred k (x :: l)

@[expose] def avoidListX (n : Nat) (O F : List Nat) : List Nat :=
  (F.filter fun m => m != 0 && !(m ∈ O)).filter fun m => decide (m < 2 ^ n)

@[expose] def avoidK (n b : Nat) (O F : List Nat) : Bool :=
  fGX (avoidListX n O F) (fun l => (subX l).any fun x => x ∈ O) (b + 1) []

end CFSG.KC.HMathieu

end
