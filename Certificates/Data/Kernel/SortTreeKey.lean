module

public import Certificates.Data.Kernel.SortTree

public section

namespace CFSG.KC.SortTree

open CFSG.KLie.CT

@[expose] noncomputable def hiIncK (rec : Nat → Nat) (n wv s : Nat) : Bool :=
  allN (Nat.sub n 1) fun i => Nat.blt (Nat.shiftRight (valF wv (rec i)) s)
    (Nat.shiftRight (valF wv (rec (Nat.succ i))) s)

end CFSG.KC.SortTree

end
