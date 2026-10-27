module

public import Certificates.Data.Kernel.Ivk8NormP

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm

@[expose] noncomputable def chkPC (n w r : Nat) (ps : List Nat) (hss : List (List (Nat × Nat)))
    (L : List Nat) : Bool :=
  L.all fun y =>
    !Nat.beq (cmpF n w y r) (cmpF n w r y) || ps.all fun p => hss.all fun hs => okP n w p hs y

@[expose] def hhV {n : Nat} (y u : VP n) : Bool :=
  invoV u && invoV (conjV y u) && commV u (conjV y u) &&
    !difV (conjV y (conjV y u)) (mulV u (conjV y u)) && difV (conjV y u) u

@[expose] def hhAll {n : Nat} (us L : List (VP n)) : Bool :=
  L.all fun y => !difV y (oneV n) || us.any (hhV y)

end CFSG.KS.Ivk8NormP

end
