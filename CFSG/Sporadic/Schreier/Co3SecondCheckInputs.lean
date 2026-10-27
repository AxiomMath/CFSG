module

public import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public import CFSG.Sporadic.Schreier.Co3Outer
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Monster.B.Mathieu.Order

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu

@[expose] def co3M1CommBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3M1CommBase).map Fin.val).toArray

@[expose] def co3M112BaseArr : Array Nat :=
  ((co3FinList 12 (by decide) co3M112Base).map Fin.val).toArray

@[expose] def co3M1CommLevels : Array Level := rawLevels 276 co3M1CommArrs co3M1CommBaseArr

@[expose] def co3M112Levels : Array Level := rawLevels 12 co3M112Arrs co3M112BaseArr

@[expose] def co3ItArr : Array Nat := co3ItNat.toArray

@[expose] def co3Kappa1Gens : Array (Array Nat) :=
  Array.ofFn (n := 6) fun k => renameA 12 co3C12Arr (restrictA co3ItArr co3M1Arrs[k.val]!)

end CFSG.Sporadic.Schreier.Co3
