module

public import Certificates.Data.Kernel.Spor.HypK

public section

namespace CFSG.KS.HypK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PSearch

@[expose] noncomputable def ev1 (w d a x : Nat) : Nat :=
  nIf(Nat.beq a 0, x, nIf(Nat.beq a 1, pg w (mask w) d x, pg w (mask w) d (pg w (mask w) d x)))

@[expose] noncomputable def evD (w : Nat) (D : List Nat) (k x : Nat) : Nat :=
  ev1 w (nthN D 0) (dg3 k 0) (ev1 w (nthN D 1) (dg3 k 1) (ev1 w (nthN D 2) (dg3 k 2)
    (ev1 w (nthN D 3) (dg3 k 3) (ev1 w (nthN D 4) (dg3 k 4) x))))

@[expose] noncomputable def dInjOK (w : Nat) (D xs : List Nat) : Bool :=
  allN 243 fun k => bIf(Nat.beq k 0, true,
    List.rec (motive := fun _ => Bool) false
      (fun x _ ih => bIf(Nat.beq (evD w D k x) x, ih, true)) xs)

@[expose] noncomputable def lenOK (Yl Yp : List (List Nat)) (r : Nat) : Bool :=
  allN r fun i => bAnd(Nat.beq (List.length (nthL Yl i)) 6, Nat.beq (List.length (nthL Yp i)) 4)

end CFSG.KS.HypK

end
