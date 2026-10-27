module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.OrbRow.Defs

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow

@[expose] noncomputable def tupK (n w m idn : Nat) : List (List Nat) → List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => idn)
    (fun T _ ih ix => List.rec (motive := fun _ => Nat) idn
      (fun j rest _ => pcomp n w m (getS T j) (ih rest)) ix)

@[expose] noncomputable def fixCnt (n w m x : Nat) : Nat :=
  foldN n (fun p acc => Nat.add acc (nIf(Nat.beq (pg w m x p) p, nat_lit 1, nat_lit 0)))
    (nat_lit 0)

@[expose] noncomputable def fixNeK (n w m x y : Nat) : Bool :=
  bIf(Nat.beq (fixCnt n w m x) (fixCnt n w m y), false, true)

end CFSG.KC.HeChain

end
