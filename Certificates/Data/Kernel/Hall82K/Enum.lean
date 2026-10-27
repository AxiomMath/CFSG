module

public import Certificates.Data.Kernel.Hall82K.Affine
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.Misc.Clos

@[expose] def lane (T w m k : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul w k)) m

@[expose] noncomputable def gen2 (g0 g1 j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) g1 g0 (Nat.beq j 0)

@[expose] noncomputable def enumAt (g0 g1 N : Nat) (E PA SG CT : Nat → Nat) (k : Nat) : Bool :=
  andB (treeAt compL idK (gen2 g0 g1) 2 E PA k)
    (andB (sortAt N E SG k) (closedAt compL (gen2 g0 g1) 2 N E CT k))

end CFSG.KC.Hall82K
