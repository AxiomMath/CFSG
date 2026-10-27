module

public import Certificates.Data.Kernel.GL33T

public noncomputable section

namespace CFSG.KC.GL33T

open CFSG.KC.GL33K

@[expose] def nonemptyT {α : Type} (L : List α) : Bool := List.rec false (fun _ _ _ => true) L

@[expose] def shapeK (g : List Nat) (kind : Nat) (chs : List (List (Nat × Nat × List (List Nat)))) :
    Bool :=
  allK detT g && allK (fun grp => allK (fun c =>
    Nat.blt c.1 2 || (!Nat.beq kind 1 && nonemptyT c.2.2)) grp) chs

end CFSG.KC.GL33T

end
