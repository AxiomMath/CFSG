module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import Certificates.Data.TabCo1Reps

public section

namespace Timmesfeld.Co1FiveComp

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.TwoBNative
  Timmesfeld.Co1Five

set_option compiler.extract_closed false

@[expose] def sWords : Array (List Int) := #[
  [134, -133, 135, -71],
  [-134, 133, 135, 71, -133],
  [134, -135, -71],
  [-134, -134, 133, 71, 71],
  [134, 133, -135, -71, -133]]

@[expose] def sIdx : Array (Nat × Nat) := #[(4, 2), (3, 0), (4, 3), (1, 2), (0, 3)]

@[expose] def invW (w : List Int) : List Int := (w.map fun j => -j).reverse

@[expose] def sRows (rs is : List Rows) : List Rows := sWords.toList.map (word rs is)

@[expose] def perfAt (rs is : List Rows) (i : Nat) : Bool :=
  let w := sWords[i]!
  let j := (sIdx[i]!).1
  let k := (sIdx[i]!).2
  let b1 := a0Row rs (repA.getD 1 0)
  let b2 := a0Row rs (repB.getD 1 0)
  w.all (· != 0) &&
    mul (word rs is w) b1 == mul b1 (word rs is w) &&
    mul (word rs is w) b2 == mul b2 (word rs is w) &&
    word rs is w == word rs is (sWords[j]! ++ sWords[k]! ++ invW sWords[j]! ++ invW sWords[k]!)

@[expose] def a5OK (rs is : List Rows) : Bool :=
  gtOK (sRows rs is).toArray (gtBFS (sRows rs is).toArray 100000) &&
    (gtBFS (sRows rs is).toArray 100000).pts.size == 60 &&
    (List.range 5).all fun i =>
      decide ((sIdx[i]!).1 < 5) && decide ((sIdx[i]!).2 < 5) && perfAt rs is i

@[expose] def cenOK (rs : List Rows) : Bool :=
  let A := (List.range 125).map (a0Row rs)
  (qTree rs).pts.all fun q =>
    A.contains q || decide ((A.filter fun a => mul a q == mul q a).length ≤ 5)

@[expose] def compOK (aR bR : Rows) : Bool :=
  let d := gDag aR bR
  d.2.2 && a0Row d.1 (repA.getD 1 0) == CFSG.HardMathSupport.Dickson.I271.TabCo1.repD0 &&
    (List.range 3).all (fun j => (qTree d.1).pts.contains (rowAt d.1 (idxD.getD j 0))) &&
    cenOK d.1 && a5OK d.1 d.2.1

end Timmesfeld.Co1FiveComp
