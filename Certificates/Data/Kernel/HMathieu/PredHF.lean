module

public import Certificates.Data.Kernel.HMathieu.Normal
public import Mathlib.Data.Nat.Log

public section

namespace CFSG.KC.HMathieu

@[expose] noncomputable def predHF24K (E P L S : List Nat) (st : List (List Nat) × List Nat) :
    Bool :=
  let k := L.length
  let d := Nat.log 2 st.2.length
  (k == 0 || !decide (11 - d ≤ k + 1) || decide (7 ≤ 11 - d)) &&
    (k != 4 || decide (7 ≤ 11 - d)) && (k != 6 || (d % 2 == 0 && normK E P L S))

@[expose] noncomputable def predHF22K (E P L S : List Nat) (st : List (List Nat) × List Nat) :
    Bool :=
  let k := L.length
  let d := Nat.log 2 st.2.length
  (k == 0 || !decide (10 - d ≤ k + 1) || decide (6 ≤ 10 - d)) && (k != 5 || normK E P L S)

end CFSG.KC.HMathieu

end
