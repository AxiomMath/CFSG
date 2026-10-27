module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def plusFactorsAgens : Array (Array ℕ) := #[
  #[12, 21, 29, 20, 48, 19, 42, 59, 28, 0, 11, 9, 10, 18, 58, 56, 37, 27, 57, 35, 44, 17, 14, 8,
    4, 1, 31, 25, 41, 47, 13, 6, 22, 15, 36, 50, 24, 49, 30, 53, 33, 55, 45, 3, 54, 26, 32, 39,
    34, 7, 52, 40, 5, 2, 43, 23, 51, 38, 46, 16],
  #[35, 58, 55, 8, 21, 16, 41, 45, 10, 39, 3, 23, 48, 33, 28, 30, 38, 24, 17, 57, 12, 44, 6, 53,
    18, 40, 49, 13, 43, 26, 59, 2, 51, 27, 0, 34, 19, 52, 5, 50, 46, 22, 32, 14, 4, 56, 25, 37,
    20, 29, 9, 42, 47, 11, 1, 31, 7, 36, 54, 15]]

@[expose] def plusFactorsBgens : Array (Array ℕ) := #[
  #[7, 17, 39, 38, 33, 6, 0, 8, 5, 49, 16, 37, 59, 58, 36, 43, 41, 25, 46, 42, 30, 27, 34, 52, 40,
    21, 11, 1, 19, 53, 14, 9, 48, 54, 56, 45, 51, 55, 22, 29, 44, 35, 12, 57, 13, 10, 4, 2, 15,
    23, 26, 20, 31, 47, 18, 50, 3, 32, 24, 28],
  #[46, 49, 3, 6, 56, 17, 11, 34, 41, 58, 22, 14, 32, 38, 2, 19, 24, 59, 30, 27, 42, 7, 53, 28,
    15, 37, 12, 16, 55, 20, 57, 10, 39, 5, 40, 25, 33, 4, 18, 54, 52, 23, 9, 31, 45, 0, 47, 44,
    51, 48, 1, 50, 21, 43, 26, 8, 35, 13, 29, 36]]

@[expose] def plusFactorsCA (_ : Unit := ()) : ArrCert := enumBfs 60 plusFactorsAgens plusBase 100

@[expose] def plusFactorsCB (_ : Unit := ()) : ArrCert := enumBfs 60 plusFactorsBgens plusBase 100

@[expose] def plusFactorsEnumA (_ : Unit := ()) : Bool :=
  enumOK 60 plusFactorsAgens plusBase (plusFactorsCA ())

@[expose] def plusFactorsEnumB (_ : Unit := ()) : Bool :=
  enumOK 60 plusFactorsBgens plusBase (plusFactorsCB ())

@[expose] def plusFactorsSizeA (_ : Unit := ()) : Bool := (plusFactorsCA ()).pts.size == 60

@[expose] def plusFactorsSizeB (_ : Unit := ()) : Bool := (plusFactorsCB ()).pts.size == 60

@[expose] def plusFactorsSimpleA (_ : Unit := ()) : Bool :=
  conjSimpleOK 60 plusBase (plusFactorsCA ())

@[expose] def plusFactorsSimpleB (_ : Unit := ()) : Bool :=
  conjSimpleOK 60 plusBase (plusFactorsCB ())

@[expose] def plusFactorsTableOK (_ : Unit := ()) : Bool :=
  allLt 60 fun i => validA 60 plusTable[i]!

@[expose] def plusFactorsMemGens (_ : Unit := ()) : Bool :=
  let E := plusEnum ()
  (allLt plusFactorsAgens.size fun k => E.pts.toList.any (eqA 60 plusFactorsAgens[k]!)) &&
    (allLt plusFactorsBgens.size fun k => E.pts.toList.any (eqA 60 plusFactorsBgens[k]!))

@[expose] def plusFactorsCommGens (_ : Unit := ()) : Bool :=
  allLt plusFactorsAgens.size fun i => allLt plusFactorsBgens.size fun j =>
    eqA 60 (commutatorA 60 plusFactorsAgens[i]! plusFactorsBgens[j]!) (idA 60)

@[expose] def plusFactorsDisjoint (_ : Unit := ()) : Bool :=
  let cA := plusFactorsCA ()
  let cB := plusFactorsCB ()
  allLt cA.pts.size fun i => allLt cB.pts.size fun j =>
    (eqA 60 cA.pts[i]! cB.pts[j]!) == false || eqA 60 cA.pts[i]! (idA 60)

@[expose] def plusFactorsConjGens (_ : Unit := ()) : Bool :=
  let cA := plusFactorsCA ()
  let cB := plusFactorsCB ()
  allLt 60 fun i =>
    (allLt plusFactorsAgens.size fun k =>
      cB.pts.toList.any (eqA 60 (conjA 60 plusTable[i]! plusFactorsAgens[k]!))) &&
    (allLt plusFactorsBgens.size fun k =>
      cA.pts.toList.any (eqA 60 (conjA 60 plusTable[i]! plusFactorsBgens[k]!)))

@[expose] def plusFactorsNonabelian (_ : Unit := ()) : Bool :=
  (eqA 60 (commutatorA 60 plusFactorsAgens[0]! plusFactorsAgens[1]!) (idA 60)) == false

@[expose] def plusFactorsRowMem (p : Array ℕ) : Bool :=
  (List.range 60).any fun i => eqA 60 plusTable[i]! p

@[expose] def plusFactorsProdMem (p : Array ℕ) : Bool :=
  (List.range 60).any fun i => (List.range 60).any fun j =>
    decide (i ≠ j) && decide ((plusTable[i]!)[j]! = j) &&
      eqA 60 (compA 60 plusTable[i]! plusTable[j]!) p

@[expose] def plusFactorsEnumMem (c : ArrCert) (p : Array ℕ) : Bool :=
  c.pts.toList.any (eqA 60 p)

@[expose] def plusFactorsInvolutions (_ : Unit := ()) : Bool :=
  let E := plusEnum ()
  let cA := plusFactorsCA ()
  let cB := plusFactorsCB ()
  allLt E.pts.size fun k =>
    let p := E.pts[k]!
    (eqA 60 (compA 60 p p) (idA 60)) == false || eqA 60 p (idA 60) ||
      plusFactorsRowMem p || plusFactorsProdMem p ||
        plusFactorsEnumMem cA p || plusFactorsEnumMem cB p

end CFSG.OddTranspositions.PartThree
