module

public section

namespace CFSG.KC.HMathieu

@[expose] def fixEqK (k : Nat) (U : List Nat) (L _S : List Nat)
    (st : List (List Nat) × List Nat) : Bool :=
  L.length != k || st.2 == U

end CFSG.KC.HMathieu

end
