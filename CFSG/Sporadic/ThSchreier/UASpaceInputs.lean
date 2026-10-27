
module

public import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def uaRowsTxt : List ℕ := hexsOf (include_str "Data/UAFactor.txt")

@[expose] def uaBlock (k : ℕ) : Array V4 :=
  Array.ofFn (n := 248) fun i => v4OfNat (uaRowsTxt.getD (248 * k + i.val) 0)

@[expose] def rowsUAP : Array V4 := uaBlock 0

@[expose] def rowsUAQ : Array V4 := uaBlock 1

@[expose] def rowsUAPInv : Array V4 := uaBlock 2

@[expose] def rowsUAQInv : Array V4 := uaBlock 3

@[expose] def rowsAmI : Array V4 := Array.ofFn (n := 248) fun i => (rowsA[i]!).xor (idRows[i]!)

@[expose] def rowsD120 : Array V4 := Array.ofFn (n := 248) fun i =>
  if i.val < 120 then idRows[i.val]! else V4.zero

end CFSG.Sporadic.ThSchreier
