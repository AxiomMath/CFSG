module

public import Certificates.Data.CFSGNative.AS91.M24FixOct

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def mulTabF (a b : Array Nat) : Array Nat :=
  ((List.range 24).map fun i => a.toList.getD (b.toList.getD i 0) 0).toArray

@[expose] def tabKeyF (t : Array Nat) : Nat := t.toList.foldl (fun acc m => (acc <<< 8) ||| m) 0

@[expose] def fixOctStepsF : List (Array Nat → Array Nat) :=
  [mulTabF Native.fixOctComm1, mulTabF Native.fixOctComm2]

@[expose] def invTabF (a : Array Nat) : Array Nat :=
  ((List.range 24).map fun v => ((List.range 24).find? fun i => a.toList.getD i 0 == v).getD 0).toArray

@[expose] def fixOctCommF : Bool :=
  (mulTabF Native.fixOctA1 (mulTabF Native.fixOctB1
      (mulTabF (invTabF Native.fixOctA1) (invTabF Native.fixOctB1))) == Native.fixOctComm1) &&
    (mulTabF Native.fixOctA2 (mulTabF Native.fixOctB2
      (mulTabF (invTabF Native.fixOctA2) (invTabF Native.fixOctB2))) == Native.fixOctComm2)

namespace FixOctEq

scoped instance (priority := high) decEqArr : DecidableEq (Array Nat) :=
  fun a b => decidable_of_iff (a.toList = b.toList) Array.toList_inj

end FixOctEq

end CFSG.KC.M24G
