module

public import Certificates.Data.Kernel.F2TriSep

public section

namespace CFSG.KC.F2OrbW

open CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2TriSep

@[expose] noncomputable def wordsToK (d A B v : Nat) (P : List (Nat × List Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => Prod.rec (motive := fun _ => Bool) (fun t w =>
      Nat.beq (vmF d (trK d (wordB d A B w (idF d))) v) t && ih) e) P

end CFSG.KC.F2OrbW

end
