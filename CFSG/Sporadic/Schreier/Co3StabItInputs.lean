module

public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SylowCheckInputs

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3StabItText : String := include_str "Co3StabIt.txt"

@[expose] def co3StabItArrs : Array (Array Nat) :=
  Array.ofFn (n := 8) fun j => hexLine co3StabItText.toUTF8 3 276 j.val

@[expose] def co3StabItBase : List Nat := [35, 41, 43, 79, 80, 108, 0]

@[expose] def co3StabItBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3StabItBase).map Fin.val).toArray

@[expose] def co3StabItDerivations : List (List Int) := []

@[expose] def co3StabItLevels : Array Level := rawLevels 276 co3StabItArrs co3StabItBaseArr

end CFSG.Sporadic.Schreier.Co3
