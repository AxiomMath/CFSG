module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native

abbrev heDeg : Nat := 8330

@[expose] def heGenHex : String := include_str "Data"/"CertGens.txt"

@[expose] def heStrongHex : String := include_str "Data"/"CertStrong.txt"

@[expose] def heGen (k : Nat) : Array Nat := hexTable 4 8330 (8330 * k) heGenHex

@[expose] def heStrong (j : Nat) : Array Nat := hexTable 4 8330 (8330 * j) heStrongHex

@[expose] def heStrongArrs : Array (Array Nat) := Array.ofFn fun j : Fin 9 => heStrong j.val

@[expose] def heGenArrs : Array (Array Nat) := Array.ofFn fun k : Fin 2 => heGen k.val

@[expose] def heBase : List Nat := [0, 1, 2, 3, 4]

@[expose] def heWords : Array (List Int) :=
  #[[], [], [-2, 1, -2, 1, 2, 1, 2], [3, 1, 3, 1, 3, 1], [2, 1, 2, 2], [1, -5, 3, 1, 3, 5],
    [1, -5, -5, 3, -5, -5, 3, 5, 5, 5, 5, 5, 3, 5], [7, 3],
    [-6, -6, 3, -5, -5, 3, -5, -5, 1, -5, 3, 5, 5, 1, 3, 5, 3, 5]]

end CFSG.Sporadic.HeldB
