module

public import Certificates.Data.Kernel.Griess13.Packed
public import CFSG.Monster.GMS.Griess13.ChecksGlueInputs

public section

namespace CFSG.KC.G13

open CFSG.KC.Co1B CFSG.Monster.GMS.Griess13.Co1Data CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def ofBitsR (d : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 j)) (f j)) d

@[expose] noncomputable def eqMaskK (X i j : Nat) : Nat :=
  ofBitsR 576 fun a => ((a / 24 == i) && X.testBit (24 * (a % 24) + j)) !=
    ((a % 24 == j) && (decide (a / 24 < 24) && X.testBit (24 * i + a / 24)))

@[expose] noncomputable def foldXorL (μ : Nat) (E : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun e _ ih k acc => ih (Nat.succ k)
      (Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc e) (Nat.testBit μ k))) E

@[expose] noncomputable def spanCheckL (E : List Nat) (fmask : Nat) (cert : Nat → Nat × Nat) : Bool :=
  (List.range 576).all fun a => fmask.testBit a ||
    (foldXorL (cert a).1 E 0 0 == ((1 <<< a) ^^^ (cert a).2) && ((cert a).2 ||| fmask) == fmask)

@[expose] def comboK (T : List Nat) (c : Fin 8 → ZMod 2) : Nat :=
  (List.range 8).foldl (fun acc i => if cF c i = 1 then acc ^^^ T.getD i 0 else acc) 0

@[expose] noncomputable def powW (a : Nat) : Nat → Nat
  | 0 => CFSG.KC.Co1B.oneK
  | n + 1 => mulWK (powW a n) a

end CFSG.KC.G13

end
