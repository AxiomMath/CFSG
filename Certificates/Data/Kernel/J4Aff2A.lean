module

public import Certificates.Data.Kernel.J4TreeNode

public section

namespace CFSG.KC.J4Aff2A

open CFSG.KC.J4TreeN

@[expose] noncomputable def clsOK (T : Tabs) (K : Nat) (y : Nat × Nat × Nat × Nat) (w : Nat) :
    Bool :=
  let X := M (T.eta y.1) K
  let N := T.eta y.2.2.1
  Nat.blt y.1 2048 && Nat.blt y.2.2.1 2048 &&
    ((is2AK T.sx N 0 && is2AK T.sx X w) || (non2AK T.sx N 0 && non2AK T.sx X w))

@[expose] noncomputable def clsAll (T : Tabs) (K : Nat) :
    List (Nat × Nat × Nat × Nat) → Nat → Bool
  | [], _ => true
  | y :: ys, ws => clsOK T K y (ws % 4096) && clsAll T K ys (ws / 4096)

@[expose] noncomputable def entOK (T : Tabs) (W : Nat → Nat) :
    Nat → List (Nat × Nat × List (Nat × Nat × Nat × Nat)) → Bool
  | _, [] => true
  | j, x :: D => Nat.blt x.1 1024 && clsAll T (T.kel x.1) x.2.2 (W j) && entOK T W (j + 1) D

@[expose] noncomputable def allOK (T : Tabs) (D : List (Nat × Nat × List (Nat × Nat × Nat × Nat)))
    (W : Nat → Nat) : Bool :=
  entOK T W 0 D

end CFSG.KC.J4Aff2A

end
