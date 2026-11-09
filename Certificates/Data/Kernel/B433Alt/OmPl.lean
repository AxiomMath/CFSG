module

public import Certificates.Data.Kernel.B433Alt.Om

public section

namespace CFSG.KC.B4A

@[expose] noncomputable def wordPl19 (MS : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun c _ ih X => sN (netApp19 MS c X) ih) w

@[expose] noncomputable def relPlOK (MS : Nat → Nat) (w : List Nat) (u : Nat) : Bool :=
  Nat.beq (wordPl19 MS w (CFSG.KC.MonsterConv.Perm.idPlane OW u))
    (CFSG.KC.MonsterConv.Perm.idPlane OW u)

end CFSG.KC.B4A

end
