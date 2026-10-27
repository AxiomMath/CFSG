module

public import Certificates.Data.Kernel.HMathieu.PickK
public import Certificates.Data.Kernel.HMathieu.FixCert

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def pickJ (n : Nat) (M : List Nat) : List Nat :=
  ((List.range n).foldl (fun (st : List Nat × List Nat) j =>
    bif Nat.beq (reduceK st.1 (actM M (2 ^ j) ^^^ 2 ^ j)) 0 then st
    else (insK (reduceK st.1 (actM M (2 ^ j) ^^^ 2 ^ j)) st.1, j :: st.2)) ([], [])).2

@[expose] noncomputable def rankJ (n r : Nat) (M J : List Nat) : Bool :=
  Nat.beq J.length r && J.all (fun j => Nat.blt j n) && imgOK M J

@[expose] noncomputable def rankOK (n r : Nat) (M : List Nat) : Bool :=
  rankJ n r M ((pickJ n M).take r)

end CFSG.KC.HMathieu

end
