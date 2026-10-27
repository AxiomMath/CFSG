module

public import CFSG.Sporadic.Schreier.LyCheckOrbit

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

set_option compiler.extract_closed false

@[expose] def sepIdx : Array Nat := #[2420579, 6905316, 584305, 4659222, 4620042, 186312,
  1689574, 5043494, 5482467, 1369437, 2585, 3571874, 5206439, 6853676, 6950565, 4342028]

@[expose] def sepKeysTxt : String := include_str "LySepKeys.txt"

@[expose] def sepYTxt : String := include_str "LySepY.txt"

@[expose] def sepCinvTxt : String := include_str "LySepCinv.txt"

@[expose] def sepVecTxt : String := include_str "LySepVec.txt"

@[expose] def sepTreeTxt : String := include_str "LySepTree.txt"

@[expose] def txtLines (s : String) : Array String :=
  ((s.splitOn "\n").filter (· != "")).toArray

@[expose] def sepKeys : Array ByteArray :=
  (txtLines sepKeysTxt).map fun s =>
    let d := digitsOf s
    encodeDigits fun p => if p < 826 then d[p]! else 0

@[expose] def sepY : Array (Array Nat) := matOfDigits (sepYTxt.replace "\n" "")

@[expose] def sepCinv : Array (Array Nat) := matOfDigits (sepCinvTxt.replace "\n" "")

@[expose] def sepV : Array Nat := digitsOf ((txtLines sepVecTxt).getD 0 "")

@[expose] def sepW : Array Nat := digitsOf ((txtLines sepVecTxt).getD 1 "")

@[expose] def sepPar : Array Nat := parseNats ((txtLines sepTreeTxt).getD 0 "")

@[expose] def sepOp : Array Nat := parseNats ((txtLines sepTreeTxt).getD 1 "")

@[expose] def sepAB : Nat × Nat := (0, 3)

@[expose] def sepMu : Nat := 4

@[expose] def sepFaithCertificate (_ : Unit) : Bool :=
  faithChecks sepKeys formF sepY sepCinv sepV sepW sepPar sepOp sepAB sepMu

end CFSG.Sporadic.LySchreier.Native
