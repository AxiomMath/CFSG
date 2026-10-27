module

public import Certificates.Data.Th687.MFactsB
public import Certificates.Data.Th687.MFactsC

public section

namespace CFSG.Sporadic.Th.Recog.MFactsDData

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Recog.MFactsBData CFSG.Sporadic.Th.Recog.MFactsCData

@[expose] def checkT3687008 (_ : Unit := ()) : Bool :=
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let W1 := rowsW1 D E
  let W2 := rowsW2 U W1 (rowsUI U)
  (commFilter (mulRows W1 W2)).all fun k =>
    decide (k.val ≤ 1) || !eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows

@[expose] def checkT333687008 (_ : Unit := ()) : Bool :=
  let D := rowsWJ 3
  let E := rowsWJ 4
  let W1 := rowsW1 D E
  (commFilter W1).all fun k =>
    decide (k.val ≤ 1) || !eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows

@[expose] def centSList (_ : Unit := ()) : List (Fin 512) := commFilter (rowsWJ 5)

end CFSG.Sporadic.Th.Recog.MFactsDData
