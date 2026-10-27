module

public import Certificates.Data.Kernel.Co1Three.Slp

public section

namespace CFSG.KC.Co1Cl

@[expose] noncomputable def allLtK (st : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(Nat.blt s st, ih)) S

@[expose] noncomputable def seedsBelowK (CH : List (Nat × Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Prod.rec (motive := fun _ => Bool)
      (fun st r => Prod.rec (motive := fun _ => Bool) (fun _ S => bAnd(allLtK st S, ih)) r) x) CH

end CFSG.KC.Co1Cl

end
