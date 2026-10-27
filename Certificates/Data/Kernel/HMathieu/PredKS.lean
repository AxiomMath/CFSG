module

public import CFSG.Quasithin.Background.HLU24Inputs
public import CFSG.Quasithin.Background.HFixSylBase

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.LU24

@[expose] def predKSK (st : List (List Nat) × List Nat) : Bool :=
  st.1.length != 6 || st.2.length != 16 || st.2 == uSMasks

end CFSG.KC.HMathieu

end
