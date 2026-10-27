module

public import Certificates.Data.Kernel.Misc.E6Std

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def snocN (l : List Nat) (y : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons y List.nil) (fun x _ ih => List.cons x ih) l

@[expose] noncomputable def conjStepK (G Gi : Nat → Nat) (steps : List (Nat × Nat)) (acc : List Nat) :
    Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun s _ ih acc => Prod.rec (motive := fun _ => Bool) (fun p j =>
      andB (Nat.blt p (lenN acc))
        (letB (mulB (mulB (G j) (nthV acc p)) (Gi j)) fun y =>
          andB (notB (memN y acc)) (ih (snocN acc y)))) s) steps acc

@[expose] noncomputable def conjOrbK (a ai b bi : Nat) (steps : List (Nat × Nat)) (z : Nat) : Bool :=
  letB a fun a => letB ai fun ai => letB b fun b => letB bi fun bi => letB z fun z =>
    conjStepK (fun j => Bool.rec (motive := fun _ => Nat) b a (Nat.beq j 0))
      (fun j => Bool.rec (motive := fun _ => Nat) bi ai (Nat.beq j 0)) steps (List.cons z List.nil)

end CFSG.KC.Misc.E6Std

end
