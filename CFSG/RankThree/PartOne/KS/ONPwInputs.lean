module

public import CFSG.Sporadic.Schreier.ONCheckChainInputs
public import CFSG.Sporadic.Schreier.ONOuterData
public import CFSG.RankThree.Native.ONSevenData
public import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import CFSG.Sporadic.Schreier.ONCheckChainInputs
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import CFSG.RankThree.Native.ONSevenData
public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload

public section

namespace CFSG.RankThree.PartOne.ONPw

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.RankThree.Native
  CFSG.Sporadic.ONOddCore

set_option compiler.extract_closed false

@[expose] def sInv : Array (Array Nat) := pinvs nPts qonStrongArrs

@[expose] def wArr (w : List Int) : Array Nat := pword nPts qonStrongArrs sInv w

@[expose] def zW : List Int := CFSG.ONSchreier.Data.zWord

@[expose] def y0W : List Int := (onSevenCentWords[0]!)[3]!

@[expose] def x0W : List Int := onSevenLineWords[0]!

@[expose] def bW : List Int := [-5, -2, -4, 7, -2, 4, -3, 5, 3, -5]

@[expose] def kW (j : Nat) : List Int := (onSevenCentWords[0]!)[j]!

@[expose] def yLetters : List Nat := [2, 3, 2, 3, 2, 3, 2, 2, 2, 3, 3, 2, 2, 2, 3]

@[expose] def liftWords : List (List (List Nat)) :=
  (localCert.records.flatMap QuotRecord.lifts).map LiftEntry.words

@[expose] def nLifts : Nat := 16

@[expose] def baseA : Array Nat := #[0, 227759, 100817]

@[expose] def wF : List Nat := [0, 6, 5, 4, 2, 2, 4, 2, 0, 5]

end CFSG.RankThree.PartOne.ONPw
