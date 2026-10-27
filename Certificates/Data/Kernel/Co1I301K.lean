module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Certificates.Data.Kernel.Co1B
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KC.Co1I301

open CFSG.KLie.CT

@[expose] noncomputable def zipK (A : List Nat) : List Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => List Nat → List (Nat × Nat)) (fun _ => [])
    (fun a _ ih B => List.rec (motive := fun _ => List (Nat × Nat)) [] (fun b B' _ => (a, b) :: ih B')
      B) A

@[expose] noncomputable def eqListK (F : Nat → Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih k => andB (Nat.beq a (F k)) (ih (Nat.succ k))) L

@[expose] noncomputable def relK (x y xi yi : Nat) (w : List (Fin 2 × Bool)) : Nat :=
  w.foldl (fun acc l => CFSG.KC.Co1B.mulWK acc (if l.1 = 0 then (if l.2 then x else xi) else
    (if l.2 then y else yi))) CFSG.KC.Co1B.oneK

@[expose] noncomputable def impAllK (p q : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (orB (notB (p x)) (q x)) ih) L

end CFSG.KC.Co1I301

end
