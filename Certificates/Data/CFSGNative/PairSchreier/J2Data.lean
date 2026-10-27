module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Schreier.PairNative

open CFSG.Monster.B.Co2.Native

@[expose] def j2StrongHex : String := include_str "J2Strong.txt"

@[expose] def j2Strong (j : Nat) : Array Nat := hexTable 4 315 (315 * j) j2StrongHex

@[expose] def j2StrongArrs (_ : Unit := ()) : Array (Array Nat) := Array.ofFn fun j : Fin 7 => j2Strong j.val

@[expose] def j2Base : List Nat := [1, 0, 2]

@[expose] def j2Words (_ : Unit := ()) : Array (List Int) :=
  #[[], [], [-2, -2, 1, 2, 2], [-2, 1, -2, -2, 1, 2, 2, 1, 2], [1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1],
    [3, 5, 3, 4, 3, 4], [3, 4, 3, 5, 3, 4]]

end CFSG.Sporadic.Schreier.PairNative
