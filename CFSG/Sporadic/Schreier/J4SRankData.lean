
module

public import CFSG.Sporadic.Schreier.J4SThreeDataInputs

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

@[expose] def Q3GenPairs : Array Pair :=
  #[powP (wordP Xn Yn q3Words[0]!) q3Exps[0]!, powP (wordP Xn Yn q3Words[1]!) q3Exps[1]!]

@[expose] def q3PairK (kp : Array Pair) (k : ℕ) : Pair :=
  if _h : 0 < k ∧ (q3Par[k]!)[0]! < k then
    mulP (q3PairK kp (q3Par[k]!)[0]!) kp[(q3Par[k]!)[1]!]!
  else oneP
termination_by k
decreasing_by exact _h.2

@[expose] def comb3 (a b c i : ℕ) : ℕ :=
  (if i % 2 = 1 then a else 0) ^^^ (if i / 2 % 2 = 1 then b else 0) ^^^
    (if i / 4 % 2 = 1 then c else 0)

@[expose] def rows3OK (X : Array ℕ) : Bool :=
  let a := X[0]! ^^^ 1
  let b := X[1]! ^^^ 2
  let c := X[2]! ^^^ 4
  decide (a < 2 ^ 112) && decide (b < 2 ^ 112) && decide (c < 2 ^ 112) &&
    (List.range 8).all fun i => (List.range 8).all fun j =>
      i == j || comb3 a b c i != comb3 a b c j

@[noinline, expose] def q3RowsOK (kp : Array Pair) : Bool :=
  (List.range 26).all fun k => rows3OK (q3PairK kp (k + 1)).1

end CFSG.Sporadic.J4Schreier
