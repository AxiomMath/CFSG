module

public import Certificates.Data.Co1FiveComp
public import Certificates.Data.Kernel.Co1Seven.Perf

public section

namespace Timmesfeld.Co1FiveComp

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier.Native
open Timmesfeld.Co1SevenPerfect (encW)

@[expose] def commW5 (i : Nat) : List Int :=
  sWords[(sIdx[i]!).1]! ++ sWords[(sIdx[i]!).2]! ++ invW sWords[(sIdx[i]!).1]! ++
    invW sWords[(sIdx[i]!).2]!

@[expose] noncomputable def SG (M MI : Nat → Nat) (l : Nat) : Nat := wordWK M MI (encW sWords[l]!)

@[expose] noncomputable def compKAt (M MI : Nat → Nat) (B1 B2 i : Nat) : Bool :=
  let w := sWords[i]!
  let c := commW5 i
  let X := wordWK M MI (encW w)
  decide ((sIdx[i]!).1 < 5) && decide ((sIdx[i]!).2 < 5) && w.all (· != 0) &&
    lettersK 137 (encW w) && lettersK 137 (encW c) && decWord (encW w) == w &&
    decWord (encW c) == c && Nat.beq (mulWK X B1) (mulWK B1 X) &&
    Nat.beq (mulWK X B2) (mulWK B2 X) && Nat.beq X (wordWK M MI (encW c))

@[expose] noncomputable def cenK (AT : Nat → Nat) (t : Nat) : Bool :=
  Nat.ble ((List.range 125).filter fun k => eqU (mulWK (AT k) t) (mulWK t (AT k))).length 5

end Timmesfeld.Co1FiveComp

end
