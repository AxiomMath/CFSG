module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.IF4R

open CFSG.KC.IF4C

@[expose] noncomputable def packL (r : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add a (Nat.mul 4096 ih)) r

@[expose] noncomputable def packR (r : Array Nat) : Nat := packL r.toList

@[expose] noncomputable def subP (gs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => idP)
    (fun g _ ih x => mulP (bif Nat.beq (Nat.mod x 2) 1 then g else idP) (ih (Nat.div x 2))) gs x

section
variable (T O : List Nat) (n : Nat) (f : Nat → Nat)

@[expose] noncomputable def recOK (r : Nat) (p : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x as _ => Nat.blt x n && pathOK O as && Nat.beq (mulP (pathP T as) (f x)) r) p

@[expose] noncomputable def recsOK (rs : List Nat) (ps : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun r _ ih ps => List.rec (motive := fun _ => Bool) false
      (fun p ps' _ => recOK T O n f r p && ih ps') ps) rs ps

end

end CFSG.KC.IF4R

end
