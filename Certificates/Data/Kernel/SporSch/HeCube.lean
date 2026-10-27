module

public import Certificates.Data.Kernel.SporSch.HeSrch

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def cbK (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (F : Nat) :
    Bool :=
  eqOnL bs (fun b => nfPtT w NR NL LT PT (nat_lit 5) F (nfPtT w NR NL LT PT (nat_lit 5) F
    (nfPtT w NR NL LT PT (nat_lit 5) F b))) (fun b => b)

end CFSG.KS.SporSch

end
