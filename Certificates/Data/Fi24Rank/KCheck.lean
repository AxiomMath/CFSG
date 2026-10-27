module

public import Certificates.Data.Fi24Rank.Common
public import Certificates.Data.Fi24Rank.KData
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.FischerOddCore

set_option compiler.extract_closed false

@[expose] def kRA (_ : Unit := ()) : Array (Array Nat) := rowsOf 504 (hexNums 3 kRAText)

@[expose] def kRG (_ : Unit := ()) : Array (Array Nat) := rowsOf 504 (hexNums 3 kRGText)

@[expose] def kRMu (_ : Unit := ()) : Array (Array Nat) := rowsOf 243 (hexNums 2 kRMuText)

@[expose] def kMemOK (_ : Unit := ()) : Bool :=
  let lv := rawLevels 504 fi24KStrong fi24KBase
  let S := kRA () ++ kRG ()
  allLt 7 fun k => siftA 504 lv fi24KBase 0 S[k]!

@[expose] def kUniqOK (_ : Unit := ()) : Bool :=
  let I := iotas 504 (kRA ())
  let S := stabs 504 I
  allLt 504 fun p => uniqAt 504 I S p

@[expose] def kRankOK (_ : Unit := ()) : Bool :=
  sideOK 504 (kRA ()) (kRG ()) (kRMu ()) kRP0 9 && kMemOK () && kUniqOK ()

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
