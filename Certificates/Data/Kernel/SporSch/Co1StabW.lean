module

public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.Kernel.SporSch.Co1MatW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.SporSch.Orb

@[expose] noncomputable def wordIWK (M MI : Nat → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun z _ ih acc => strictN (CFSG.KC.Co1B.mulWK acc (letterK M MI (icode z))) ih) w idM

@[expose] noncomputable def dagIWK (M MI : Nat → Nat) (nb N : Nat) (ws : List (List Int)) : Bool :=
  bAnd(Nat.beq (Nat.add nb (lenWI ws)) N,
  bAnd(allN N (fun k => invOKW (M k) (MI k)),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih k => bAnd(lettersIK k w, bAnd(Nat.beq (wordIWK M MI w) (M k), ih (Nat.succ k))))
      ws nb))

end CFSG.KS.SporSch.M24

end
