module

public import Certificates.Data.Kernel.Ivk8TwoN

public section

namespace CFSG.KC.Ivk8N

open CFSG.KC.YoshQ

@[expose] noncomputable def centralOKN (n w : Nat) (gs : List Nat) (wd : List Int) : Bool :=
  gs.all (invOKN n w) && gs.all (fun g =>
    eqN n w (pmN n w (evalN n w gs (gs.map (invN n w)) wd) g)
      (pmN n w g (evalN n w gs (gs.map (invN n w)) wd)))

end CFSG.KC.Ivk8N

end
