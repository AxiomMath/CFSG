module

public import Certificates.Data.Kernel.AE6Tri.DefsTA

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F

@[expose] noncomputable def tabOf (G : List Nat) (S : List (List (List Nat))) (k : List Nat → Bool) :
    Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun T => k T)
    (fun lv _ ih T => forceMap lv (fun w => awN T w) ih) S G

@[expose] noncomputable def tabEq (G : List Nat) (A B : List (List (List Nat))) (R : List Nat) :
    Bool :=
  tabOf G A (fun TA => tabOf G B (fun TB =>
    allIx R (fun _ c => eqN 360 9 (gl TA c) (gl TB c)) 0))

end CFSG.KC.AE6Tri

end
