module

public import Certificates.Data.CFSGNative.AS91.M24Duad
public import Certificates.Data.Kernel.M24G.FixOct
public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Todd

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G CFSG.KC.ONanSmall

@[expose] def duadKeyF (t : Array Nat) : Nat := t.toList.foldl (fun acc x => acc * 24 + x) 0

@[expose] def duadStepsF (gens : List (Array Nat)) : List (Array Nat → Array Nat) :=
  gens.map mulTabF

@[expose] def duadPpStepsF : List (Nat → Nat) :=
  Native.duadPpGens.map fun g => toddActF (imgTab g.toList)

@[expose] def duadValidT (t : Array Nat) : Bool :=
  t.size == 24 && t.toList.all fun x => decide (x < 24)

@[expose] def duadGensOK (gens : List (Array Nat)) : Bool := gens.all duadValidT

@[expose] def duadEqT (a b : Array Nat) : Bool := a.toList == b.toList

@[expose] def duadInvRow (pos : KTree (Nat × Nat)) (x y : Array Nat) : Bool :=
  duadValidT y && (findK (duadKeyF y) pos).isSome && duadEqT (mulTabF x y) Native.fixOctIdTab

@[expose] def duadInvOK (pos : KTree (Nat × Nat)) (L : List (Array Nat)) : Bool :=
  L.all fun x => duadInvRow pos x (invTabF x)

@[expose] def duadInvsF (L : List (Array Nat)) : List (Array Nat) :=
  L.filter fun x => duadEqT (mulTabF x x) Native.fixOctIdTab

@[expose] def duadBadOn (I : List (Array Nat)) : List (Array Nat) :=
  I.filter fun x => decide (32 ≤ (I.filter fun y => duadEqT (mulTabF x y) (mulTabF y x)).length)

@[expose] def duadEaF (L : List (Array Nat)) : Bool := decide ((duadBadOn (duadInvsF L)).length < 32)

@[expose] def orMask : List Nat → Nat
  | [] => 0
  | c :: l => (1 <<< c) ||| orMask l

@[expose] def duadCoverOn (K : Nat) : Bool := Native.allLt 2048 fun m => m == 0 || K.testBit m

@[expose] def duadCoverF (SL : List (List Nat)) : Bool :=
  duadCoverOn (orMask (Native.duadMasks () ++ SL.map Native.clsOf))

end CFSG.KC.M24G
