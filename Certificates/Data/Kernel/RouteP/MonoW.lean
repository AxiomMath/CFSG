module

public import Certificates.Data.Kernel.RouteP.Mono

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def roundW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (ws : List (List Int))
    (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) s
    (fun w _ ih => strictN ih (fun t => Nat.lor t (imgW NW KA KB w s))) ws

@[expose] noncomputable def closeW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (ws : List (List Int))
    (n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => strictN (roundW NW KA KB ws x) ih) n s

end CFSG.KC.RouteP

end
