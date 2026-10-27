module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.RuInsp

open CFSG.KC.Enum

@[expose] noncomputable def maskL (n w m idn : Nat) (Ps : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => idn)
    (fun b _ ih k => pcomp n w m (nIf(Nat.beq (Nat.mod k 2) 1, b, idn)) (ih (Nat.div k 2))) Ps

@[expose] noncomputable def chkKxEK (n w m idn C : Nat) (BV BE : List Nat) (kV kE : Nat) : Bool :=
  allN (Nat.pow 2 kV) (fun k => strictB (maskL n w m idn BV k) (fun v =>
    bIf(Nat.beq (pcomp n w m v C) (pcomp n w m C v),
      bIf(allN (Nat.pow 2 kE) (fun j => bIf(Nat.beq (maskL n w m idn BE j) v, false, true)),
        false, true),
      true)))

end CFSG.KC.RuInsp

end
