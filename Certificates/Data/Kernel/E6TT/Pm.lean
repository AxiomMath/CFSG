module

public import Certificates.Data.Kernel.E6TT.Weyl

public section

namespace CFSG.KC.E6TT

open Certificates.Data.E6TableT (Vec iform)

@[expose] noncomputable def pmD (H : List Nat) : List Vec := vecs (H.getD 2 0) (H.getD 0 0)

@[expose] noncomputable def pmMap (d0 x y : Vec) : Vec → Vec := fun z =>
  Bool.rec (motive := fun _ => Vec) y x (z == d0)

@[expose] noncomputable def negV (x : Vec) : Vec :=
  List.rec (motive := fun _ => Vec) [] (fun a _ ih => Int.neg a :: ih) x

@[expose] noncomputable def pmK (l : List Vec) (H : List Nat) : Bool :=
  bAnd(Nat.beq (H.getD 0 0) (nat_lit 2),
    bAnd(bIf((pmD H).getD 0 [] == (pmD H).getD 1 [], false, true),
      l.all fun x => l.all fun y =>
        bIf(iform x y == iform ((pmD H).getD 0 []) ((pmD H).getD 1 []),
          bIf(inK H (pmMap ((pmD H).getD 0 []) x y), true,
            inK H (pmMap ((pmD H).getD 0 []) (negV x) (negV y))),
          true)))

@[expose] noncomputable def pmAll (cl : List (List Vec)) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun l _ ih Hs => List.rec (motive := fun _ => Bool) false
      (fun H Hs' _ => bAnd(pmK l H, ih Hs')) Hs) cl

end CFSG.KC.E6TT

end
