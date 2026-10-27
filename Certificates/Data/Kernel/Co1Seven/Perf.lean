module

public import Certificates.Data.Co1SevenPerfect
public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.Kernel.Co1Seven.Cen

public section

namespace Timmesfeld.Co1SevenPerfect

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier.Native

@[expose] def encL (j : Int) : Nat := if 0 < j then 2 * j.toNat else 2 * (-j).toNat + 1

@[expose] def encW (w : List Int) : List Nat := w.map encL

@[expose] def commW (i : Nat) : List Int :=
  sWords[(sIdx[i]!).1]! ++ sWords[(sIdx[i]!).2]! ++ invW sWords[(sIdx[i]!).1]! ++
    invW sWords[(sIdx[i]!).2]!

@[expose] noncomputable def perfKAt (M MI : Nat → Nat) (N T i : Nat) : Bool :=
  let w := sWords[i]!
  let c := commW i
  let X := wordWK M MI (encW w)
  decide ((sIdx[i]!).1 < 6) && decide ((sIdx[i]!).2 < 6) && w.all okLetter &&
    lettersK N (encW w) && lettersK N (encW c) && decWord (encW w) == w && decWord (encW c) == c &&
    Nat.beq (mulWK X T) (mulWK T X) && Nat.beq X (wordWK M MI (encW c))

@[expose] noncomputable def perfK (M MI : Nat → Nat) (N T : Nat) : Bool :=
  !eqU (wordWK M MI (encW sWords[0]!)) idM && (List.range 6).all (perfKAt M MI N T)

end Timmesfeld.Co1SevenPerfect

end
