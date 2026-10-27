module

public import Certificates.Data.Kernel.SmithEKW
public import Certificates.Data.Kernel.Misc.T46

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.T46 (hermK)

@[expose] noncomputable def dualRow (W Y : Nat × Nat × Nat) : Bool :=
  hermK Y.1 Y.1 == 0 && hermK Y.2.1 Y.2.1 == 0 && hermK Y.2.2 Y.2.2 == 0 &&
    hermK Y.1 Y.2.1 == 0 && hermK Y.1 Y.2.2 == 0 && hermK Y.2.1 Y.2.2 == 0 &&
    hermK Y.1 W.1 == 1 && hermK Y.1 W.2.1 == 0 && hermK Y.1 W.2.2 == 0 &&
    hermK Y.2.1 W.1 == 0 && hermK Y.2.1 W.2.1 == 1 && hermK Y.2.1 W.2.2 == 0 &&
    hermK Y.2.2 W.1 == 0 && hermK Y.2.2 W.2.1 == 0 && hermK Y.2.2 W.2.2 == 1

@[expose] noncomputable def dualK : List Nat → List Nat → Bool :=
  fun D => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih Y => Nat.blt (Y.headD 0) 68719476736 && dualRow (decW x) (decW (Y.headD 0)) &&
      ih Y.tail) D

@[expose] noncomputable def keyK (M : List Nat) (R : Nat) : Bool :=
  nodupK (M.map fun m => m % R) 0

end CFSG.SmithE.K
