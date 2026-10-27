module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KS.PEnum

open CFSG.KC.Enum

@[expose] noncomputable def cntBlk (q : Nat → Bool) (b : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l s => strictN s (fun s' => nIf(q (Nat.add b l), Nat.succ s', s')))

@[expose] noncomputable def cntK (q : Nat → Bool) (hi : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun h s => strictN s (fun s' => Nat.add s' (cntBlk q (Nat.shiftLeft h (nat_lit 6)) (nat_lit 64))))
    hi

@[expose] noncomputable def lget2 (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L

end CFSG.KS.PEnum

end
