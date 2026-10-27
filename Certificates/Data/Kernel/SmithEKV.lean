module

public import Certificates.Data.Kernel.SmithEKT
public import Certificates.Data.Kernel.SmithEKE

public section

namespace CFSG.SmithE.K

@[expose] noncomputable def fixRowK (w : Nat) : List Nat → Nat → Nat → Bool :=
  fun L => List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ _ ih V M => ((V % 1048576 == w) == (M % 2 == 1)) && ih (V / 1048576) (M / 2)) L

@[expose] noncomputable def fixChunkK (C W P L : List Nat) (s n : Nat) : Bool :=
  (List.range' s n).all fun i => let w := W.getD i 0
    decide (w < 2 ^ 20) && fixRowK w L (c8ap C w) (P.getD i 0)

end CFSG.SmithE.K
