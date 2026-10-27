module

public import Certificates.Data.RkBMFi24Inv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Fi24Cfg

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi24.Native Timmesfeld.Fi24Cl
  CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv

set_option compiler.extract_closed false

@[expose] def xWords : Array (List Nat) := #[
  [18],
  [25, 22, 16, 25, 12, 14, 13, 14, 23, 18, 10, 16, 23, 8, 17, 5, 9, 6, 18, 14, 3, 13, 15, 18, 8],
  [25, 20, 17, 21, 14, 16, 20, 14, 20, 15, 8, 18, 12, 8, 14, 25, 4, 25, 4, 8, 24, 2, 17, 2, 20, 2],
  [25, 17, 19, 20, 15, 23, 21, 13, 15, 11, 16, 14, 18, 25, 7, 19, 22, 11, 19, 2, 11, 7, 23, 10],
  [25, 17, 19, 22, 20, 12, 17, 15, 15, 20, 15, 23, 8, 13, 22, 20, 10, 12, 4, 8, 11, 5, 12, 11, 2,
    11, 7, 23, 10],
  [25, 18, 20, 17, 14, 20, 14, 13, 20, 9, 18, 10, 14, 22, 6, 5, 12, 19, 12, 0, 5, 20, 10, 0, 8]]

@[expose] def nWords : Array (List Nat) := #[
  [25, 16, 14, 24, 15, 13, 15, 8, 11, 23, 14, 20, 23, 4, 8, 7, 15, 16, 9, 0, 6, 6, 15, 17],
  [25, 20, 18, 23, 13, 14, 16, 15, 17, 24, 8, 8, 22, 10, 12, 17, 4, 11, 12, 21, 9, 11, 0, 8, 4,
    16],
  [25, 23, 17, 21, 15, 15, 13, 23, 15, 18, 8, 11, 15, 20, 18, 4, 10, 5, 14, 20, 8, 2, 6, 18, 24],
  [16, 19, 22, 14, 14, 14, 12, 22, 17, 13, 10, 22, 9, 18, 12, 5, 22, 21, 23, 15, 0, 25, 15, 3, 20],
  [22, 17, 23, 13, 14, 14, 12, 16, 20, 8, 22, 21, 11, 14, 5, 14, 14, 16, 3, 21, 14, 10, 8],
  [25, 16, 13, 18, 15, 15, 18, 24, 8, 19, 21, 10, 12, 4, 16, 20, 19, 6, 0, 10, 22, 17, 6]]

@[expose] def cfgAt (L : Array Table) (i : Nat) : Bool :=
  (xWords[i]!).all (· < 26) && (nWords[i]!).all (· < 26) &&
  eqOnBase L (xWords[i]! ++ xWords[i]! ++ xWords[i]!) [] && !eqOnBase L xWords[i]! [] &&
  eqOnBase L (nWords[i]! ++ xWords[i]! ++ invWord nWords[i]!) (invWord xWords[i]!) &&
  (List.range 6).all fun j =>
    eqOnBase L (xWords[i]! ++ xWords[j]!) (xWords[j]! ++ xWords[i]!) &&
      (!decide (j < i) || eqOnBase L (nWords[i]! ++ xWords[j]! ++ invWord nWords[i]!) xWords[j]!)

@[expose] def cfgCheck (O : Enum) : Bool :=
  let L := chainLetters O
  (List.range 6).all fun i => cfgAt L i

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Fi24Cfg
