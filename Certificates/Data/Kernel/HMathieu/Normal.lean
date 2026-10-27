module

public import Certificates.Data.Kernel.HMathieu.Bfs

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def conjP (e p : Nat) : Nat := pc24 (pc24 e p) (pinvS 24 5 (mask 5) e)

@[expose] noncomputable def normK (E P L S : List Nat) : Bool :=
  E.all fun e => L.all fun a => (S.map fun s => P.getD s 0).contains (conjP e (P.getD a 0))

end CFSG.KC.HMathieu

end
