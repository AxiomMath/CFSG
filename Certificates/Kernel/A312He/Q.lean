module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HeInputs

public section

namespace CFSG.KD.A312He

open CFSG.Quasithin.A312He

@[expose] def invT (t : Array Nat) : Array Nat :=
  (List.range t.size).foldl (fun acc i => acc.set! t[i]! i) (Array.replicate t.size 0)

@[expose] def y3Lt : Array (Array Nat) := (heLetters 3 ++ (heLetters 3).map invT).toArray

@[expose] def y4Lt : Array (Array Nat) := (heLetters 4 ++ (heLetters 4).map invT).toArray

@[expose] def y7iLt : Array (Array Nat) := ((heLetters 7).map invT).toArray

@[expose] def qp1 : List (Nat × Nat) := [(0, 1)]

end CFSG.KD.A312He

end
