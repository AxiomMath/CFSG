module

public import Certificates.Data.CFSGNative.H13.J4Elems

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.J4.Native

@[inline, expose] def fixedAt (keys : ByteArray) (tab : Array V2) (i : Nat) : Bool :=
  (frApply tab (rdV2 keys i)).beq (rdV2 keys i)

@[expose] def orbFixCount (keys : ByteArray) (tab : Array V2) (n : Nat) : Nat :=
  Nat.fold n (fun i _ acc => if fixedAt keys tab i then acc + 1 else acc) 0

@[expose] def tInvRows (_ : Unit := ()) : Array V2 := (tOf (uvPairsOf basePairs)).2

end CFSG.Quasithin.H13.J4.Native
