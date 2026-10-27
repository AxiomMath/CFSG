module

public import Mathlib.Data.Nat.Log

public section

namespace CFSG.KC.HMathieu

@[expose] def predRK (n : Nat) (L _S : List Nat) (st : List (List Nat) × List Nat) : Bool :=
  L.isEmpty || decide (2 * L.length ≤ n - Nat.log 2 st.2.length)

end CFSG.KC.HMathieu

end
