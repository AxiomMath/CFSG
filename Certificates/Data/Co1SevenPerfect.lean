module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven

public section

namespace Timmesfeld.Co1SevenPerfect

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native Timmesfeld.Co1Seven
open CFSG.Sporadic.Co1.InvNative (validRows)

set_option compiler.extract_closed false

@[expose] def sWords : Array (List Int) := #[
  [-72, -71, -71, 72, -71, 72, -71, -72, -72, -71, -72, -71, 72, -71, -72, -71, -72, -71, -72,
    -72, -71],
  [72, 72, 71, 72, -71, -72, -72, -71, -72, -71, -72, -72, -71, -71, 72, 72, 72, -71],
  [-72, -71, -71],
  [-72, -71, -71, 72, -71, 72, -71, -72, -72, -71, -72, -71, 72, -71, -72, -71, -72, -71, -72,
    -72, -71, 72, -71, 72, -71, -72, -72, -71, -72, -71, 72, 72, -71],
  [-72, -71, -71, 72, -71, 72, -71, -72, -72, -71, -72, -71, 72, -71, -72, -71, -72, -71, -72,
    -72, -71, -71, -72, -71],
  [-72, -71, -71, 72, -71, 72, -71, -72, -72, -71, -72, -71, 72, -71, -72, -71, -72, -71, -72,
    -72, -71, -72, -72, 71, -72]]

@[expose] def sIdx : Array (Nat × Nat) := #[(2, 4), (3, 4), (0, 5), (1, 5), (0, 1), (2, 3)]

@[expose] def invW (w : List Int) : List Int := (w.map fun j => -j).reverse

@[expose] def okLetter (j : Int) : Bool := j == 71 || j == -71 || j == 72 || j == -72

@[expose] def perfAt (rs is : List Rows) (i : Nat) : Bool :=
  let w := sWords[i]!
  let j := (sIdx[i]!).1
  let k := (sIdx[i]!).2
  let T := rowAt rs iT
  w.all okLetter &&
    mul (word rs is w) T == mul T (word rs is w) &&
    word rs is w == word rs is (sWords[j]! ++ sWords[k]! ++ invW sWords[j]! ++ invW sWords[k]!)

@[expose] def co1PerfOK (aR bR : Rows) : Bool :=
  let d := gDag aR bR
  d.2.2 && validRows (word d.1 d.2.1 sWords[0]!) && word d.1 d.2.1 sWords[0]! != one () &&
    (List.range 6).all fun i => decide ((sIdx[i]!).1 < 6) && decide ((sIdx[i]!).2 < 6) &&
      perfAt d.1 d.2.1 i

end Timmesfeld.Co1SevenPerfect
