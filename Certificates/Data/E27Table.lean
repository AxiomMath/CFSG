module

public section

namespace CFSG.HardMathSupport.Foote.E27

@[expose] def tabMul (par : Array (Nat × Nat)) (L : Array (Array Nat)) (a b : Nat) : Nat :=
  if _h : (par[a]!).1 < a then (L[(par[a]!).2]!)[tabMul par L (par[a]!).1 b]! else b
termination_by a
decreasing_by exact _h

@[expose] def tabComm (par : Array (Nat × Nat)) (L : Array (Array Nat)) (n a : Nat) : Nat :=
  (List.range n).countP fun b => tabMul par L a b == tabMul par L b a

@[expose] def buildN {α : Type} (init : Array α) (step : Array α → Nat → α) : Nat → Array α
  | 0 => init
  | n + 1 => let a := buildN init step n; a.push (step a a.size)

@[expose] def matEqB (p d : Nat) (X Y : Array (Array Nat)) : Bool :=
  (List.range d).all fun i => (List.range d).all fun j => (X[i]!)[j]! % p == (Y[i]!)[j]! % p

end CFSG.HardMathSupport.Foote.E27
