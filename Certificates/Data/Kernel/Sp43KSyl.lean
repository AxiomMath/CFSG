module

public import Certificates.Data.Kernel.Sp43KSp
public import Certificates.Data.Kernel.Sp43KCase

public noncomputable section

namespace CFSG.KC.Sp43K

@[expose] def keyT (d g g' : Nat) : Nat :=
  min (min (conjT g g' d) (conjT g g' (powT d 2)))
    (min (conjT g g' (powT d 3)) (conjT g g' (powT d 4)))

@[expose] def sylGo (d : Nat) (R : List (Nat × Nat)) : Nat → Bool :=
  List.rec (fun _ => true)
    (fun r _ ih k => okT r.1 && okT r.2 && spT r.1 && mulT r.1 r.2 == oneT &&
      decide (k < keyT d r.1 r.2) && ih (keyT d r.1 r.2)) R

end CFSG.KC.Sp43K

end
