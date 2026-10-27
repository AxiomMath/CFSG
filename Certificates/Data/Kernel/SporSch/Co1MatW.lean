module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def invOKW (X Y : Nat) : Bool := Nat.beq (CFSG.KC.Co1B.mulWK X Y) idM

@[expose] noncomputable def wordWK (M MI : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (CFSG.KC.Co1B.mulWK acc (letterK M MI c)) ih) w idM

@[expose] noncomputable def dagWK (M MI : Nat → Nat) (nb N : Nat) (ws : List (List Nat)) : Bool :=
  bAnd(Nat.beq (Nat.add nb (lenLL ws)) N,
  bAnd(allN N (fun k => invOKW (M k) (MI k)),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih k => bAnd(lettersK k w, bAnd(Nat.beq (wordWK M MI w) (M k), ih (Nat.succ k))))
      ws nb))

end CFSG.KS.SporSch.M24

end
