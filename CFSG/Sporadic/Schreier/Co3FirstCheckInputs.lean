module

public import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public import CFSG.Sporadic.Schreier.Co3Sp6Check
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3MCommBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3MCommBase).map Fin.val).toArray

@[expose] def co3M36BaseArr : Array Nat :=
  ((co3FinList 36 (by decide) co3M36Base).map Fin.val).toArray

@[expose] def co3Sp36Levels : Array Level := rawLevels 36 co3Sp36Arrs co3Sp36BaseArr

@[expose] def co3IzArr : Array Nat := co3IzNat.toArray

@[expose] def co3KappaGens : Array (Array Nat) :=
  Array.ofFn (n := 7) fun k => renameA 36 co3CspArr (restrictA co3IzArr co3MArrs[k.val]!)

end CFSG.Sporadic.Schreier.Co3
