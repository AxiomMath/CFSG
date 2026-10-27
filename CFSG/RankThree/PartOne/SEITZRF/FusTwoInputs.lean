module

public import CFSG.LieType.Ree.LargeReeInvolutionSquare

public section

namespace CFSG.RankThree.PartOne.SEITZRF.FusTwo

open CFSG.LieType.Ree.LargeReeInvolution

@[expose] def bitLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun l => [false :: l, true :: l]

@[expose] def bit (l : List Bool) (i : ℕ) : Bool := l.getD i false

@[expose] def varBit (l : List Bool) (v : ℕ) : Bool := Nat.blt v 24 && bit l (v % 12)

@[expose] def polyBit (l : List Bool) (p : Poly) : Bool :=
  (p.filter fun m => m.all (varBit l)).length % 2 == 1

@[expose] def constPoly (b : Bool) : Poly := if b then [[]] else []

@[expose] def vWord (l : List Bool) : Word :=
  (sylowWord.map fun f => (f.1, constPoly (polyBit l f.2))).filter fun f => !f.2.isEmpty

@[expose] def isInvol (l : List Bool) : Bool :=
  (List.range 24).all fun n => !polyBit l (sqCoords.getD n [])

@[expose] def unitBits (i : ℕ) : List Bool := (List.range 12).map fun j => j == i

@[expose] def zBits : List Bool := unitBits 8

@[expose] def tBits : List Bool := unitBits 11

@[expose] def posOK (w : Word) : Bool := w.all fun f => Nat.ble 24 f.1 && Nat.ble f.1 47

@[expose] def collEq (w w' : Word) : Bool :=
  posOK w && posOK w' && collect 500 [] w == collect 500 [] w'

@[expose] def pairsOne : List (ℕ × ℕ) :=
  [(25, 26), (26, 25), (27, 34), (28, 36), (29, 35), (30, 39), (31, 38), (32, 37), (34, 27),
    (35, 29), (36, 28), (37, 32), (38, 31), (39, 30), (40, 42), (41, 41), (42, 40), (43, 44),
    (44, 43), (45, 45), (46, 47), (47, 46)]

@[expose] def pairsTwo : List (ℕ × ℕ) :=
  [(24, 31), (26, 29), (29, 26), (31, 24), (32, 32), (33, 40), (34, 37), (35, 35), (36, 43),
    (37, 34), (38, 41), (39, 46), (40, 33), (41, 38), (42, 45), (43, 36), (44, 44), (45, 42),
    (46, 39), (47, 47)]

@[expose] def relabel (pairs : List (ℕ × ℕ)) (w : Word) : Word :=
  w.map fun f => ((pairs.lookup f.1).getD 0, f.2)

abbrev Edge := List Bool × List Bool × ℕ

@[expose] def edgeCheck (e : Edge) : Bool :=
  if e.2.2 < 12 then
    collEq (vWord e.1 ++ vWord (unitBits e.2.2)) (vWord (unitBits e.2.2) ++ vWord e.2.1)
  else if e.2.2 == 12 then
    (vWord e.2.1).all (fun f => (pairsOne.lookup f.1).isSome) &&
      collEq (relabel pairsOne (vWord e.2.1)) (vWord e.1)
  else if e.2.2 == 13 then
    (vWord e.2.1).all (fun f => (pairsTwo.lookup f.1).isSome) &&
      collEq (relabel pairsTwo (vWord e.2.1)) (vWord e.1)
  else false

@[expose] def forestCheck : List Edge → List (List Bool) → Bool
  | [], _ => true
  | e :: es, known => known.contains e.2.1 && edgeCheck e && forestCheck es (e.1 :: known)

@[expose] def coverCheck (es : List Edge) : Bool :=
  (bitLists 12).all fun l =>
    !isInvol l || l.all (· == false) || l == zBits || l == tBits || es.any fun e => e.1 == l

@[expose] def fusEdges : List Edge :=
  [
    ([false, false, false, false, false, false, true, false, false, false, false, true],
      [false, false, false, false, false, false, false, false, false, false, false, true], 1),
    ([false, false, false, false, false, false, true, false, true, false, false, true],
      [false, false, false, false, false, false, true, false, false, false, false, true], 0),
    ([false, false, false, false, false, false, false, false, true, false, false, true],
      [false, false, false, false, false, false, true, false, true, false, false, true], 1),
    ([false, false, false, false, false, false, true, false, false, false, false, false],
      [false, false, false, false, false, false, false, false, true, false, false, false], 12),
    ([false, false, false, false, false, false, true, false, true, false, false, false],
      [false, false, false, false, false, false, true, false, false, false, false, false], 0),
    ([false, false, false, false, false, false, false, false, false, false, true, false],
      [false, false, false, false, false, false, false, false, false, false, false, true], 13),
    ([false, false, false, false, false, false, true, false, false, false, true, false],
      [false, false, false, false, false, false, false, false, false, false, true, false], 2),
    ([false, false, false, false, false, false, true, false, true, false, true, false],
      [false, false, false, false, false, false, true, false, false, false, true, false], 0),
    ([false, false, false, false, false, false, false, false, true, false, true, false],
      [false, false, false, false, false, false, true, false, true, false, true, false], 2),
    ([false, false, false, false, false, false, true, false, true, false, true, true],
      [false, false, false, false, false, false, false, false, false, false, true, false], 1),
    ([false, false, false, false, false, false, true, false, false, false, true, true],
      [false, false, false, false, false, false, true, false, true, false, true, true], 0),
    ([false, false, false, false, false, false, false, false, false, false, true, true],
      [false, false, false, false, false, false, true, false, false, false, true, true], 2),
    ([false, false, false, false, false, false, false, false, true, false, true, true],
      [false, false, false, false, false, false, true, false, true, false, true, true], 2),
    ([false, false, false, false, false, false, false, false, false, true, false, false],
      [false, false, false, false, false, false, false, false, false, false, true, false], 12),
    ([false, false, false, false, false, false, false, false, false, true, true, true],
      [false, false, false, false, false, false, false, false, false, true, false, false], 0),
    ([false, false, false, false, false, false, true, false, false, true, true, true],
      [false, false, false, false, false, false, false, false, false, true, true, true], 2),
    ([false, false, false, false, false, false, true, false, true, true, false, false],
      [false, false, false, false, false, false, true, false, false, true, true, true], 0),
    ([false, false, false, false, false, false, false, false, true, true, false, false],
      [false, false, false, false, false, false, false, false, false, true, false, false], 4),
    ([false, false, false, false, false, false, false, false, true, true, true, true],
      [false, false, false, false, false, false, false, false, true, true, false, false], 0),
    ([false, false, false, false, false, false, true, false, true, true, true, true],
      [false, false, false, false, false, false, false, false, true, true, true, true], 2),
    ([false, false, false, false, false, false, true, false, false, true, false, false],
      [false, false, false, false, false, false, true, false, true, true, true, true], 0),
    ([false, false, false, false, false, false, false, false, true, true, true, false],
      [false, false, false, false, false, false, false, false, false, true, true, true], 1),
    ([false, false, false, false, false, false, false, false, true, true, false, true],
      [false, false, false, false, false, false, false, false, true, true, true, false], 0),
    ([false, false, false, false, false, false, true, false, true, true, true, false],
      [false, false, false, false, false, false, false, false, true, true, true, false], 2),
    ([false, false, false, false, false, false, true, false, false, true, false, true],
      [false, false, false, false, false, false, true, false, true, true, true, false], 0),
    ([false, false, false, false, false, false, false, false, false, true, false, true],
      [false, false, false, false, false, false, false, false, true, true, false, true], 4),
    ([false, false, false, false, false, false, false, false, false, true, true, false],
      [false, false, false, false, false, false, false, false, false, true, false, true], 0),
    ([false, false, false, false, false, false, true, false, false, true, true, false],
      [false, false, false, false, false, false, false, false, false, true, true, false], 2),
    ([false, false, false, false, false, false, true, false, true, true, false, true],
      [false, false, false, false, false, false, true, false, false, true, true, false], 0),
    ([true, false, false, false, false, false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false, false, false, true, false, false], 13),
    ([true, false, false, false, true, true, true, true, true, true, true, false],
      [true, false, false, false, false, false, false, false, false, false, false, false], 2),
    ([true, false, false, false, true, true, true, true, false, true, true, true],
      [true, false, false, false, true, true, true, true, true, true, true, false], 0),
    ([true, false, false, false, true, true, true, true, true, true, true, true],
      [true, false, false, false, true, true, true, true, false, true, true, true], 10),
    ([true, false, false, false, true, true, true, true, false, true, true, false],
      [true, false, false, false, true, true, true, true, true, true, true, true], 0),
    ([true, false, false, false, false, false, false, false, true, false, false, false],
      [true, false, false, false, true, true, true, true, false, true, true, false], 2),
    ([true, false, false, false, false, false, false, false, true, false, false, true],
      [true, false, false, false, true, true, true, true, false, true, true, true], 2),
    ([true, false, false, false, false, false, false, false, false, false, false, true],
      [true, false, false, false, true, true, true, true, true, true, true, true], 2),
    ([true, false, false, false, false, false, false, false, false, false, true, true],
      [true, false, false, false, false, false, false, false, false, false, false, false], 9),
    ([true, false, false, false, true, true, false, true, true, true, false, true],
      [true, false, false, false, false, false, false, false, false, false, true, true], 2),
    ([true, false, false, false, true, true, false, true, true, true, false, false],
      [true, false, false, false, true, true, false, true, true, true, false, true], 0),
    ([true, false, false, false, true, true, false, true, false, true, false, false],
      [true, false, false, false, true, true, false, true, true, true, false, false], 10),
    ([true, false, false, false, true, true, false, true, false, true, false, true],
      [true, false, false, false, true, true, false, true, false, true, false, false], 0),
    ([true, false, false, false, false, false, false, false, true, false, true, false],
      [true, false, false, false, true, true, false, true, false, true, false, false], 2),
    ([true, false, false, false, false, false, false, false, true, false, true, true],
      [true, false, false, false, true, true, false, true, false, true, false, true], 2),
    ([true, false, false, false, false, false, false, false, false, false, true, false],
      [true, false, false, false, true, true, false, true, true, true, false, false], 2),
    ([true, false, false, true, false, false, true, true, true, true, true, true],
      [true, false, false, false, false, false, false, false, false, false, false, false], 1),
    ([true, false, false, true, true, false, true, true, false, true, false, false],
      [true, false, false, true, false, false, true, true, true, true, true, true], 0),
    ([true, false, false, true, false, false, true, true, false, true, true, true],
      [true, false, false, true, false, false, true, true, true, true, true, true], 11),
    ([true, false, false, true, true, false, true, true, true, true, false, false],
      [true, false, false, true, false, false, true, true, false, true, true, true], 0),
    ([true, false, false, true, true, true, false, false, true, true, true, true],
      [true, false, false, true, false, false, true, true, false, true, true, true], 2),
    ([true, false, false, true, false, true, false, false, true, true, true, false],
      [true, false, false, true, true, true, false, false, true, true, true, true], 0),
    ([true, false, false, true, false, true, false, false, false, true, true, false],
      [true, false, false, true, false, true, false, false, true, true, true, false], 10),
    ([true, false, false, true, true, true, false, false, false, true, true, true],
      [true, false, false, true, false, true, false, false, false, true, true, false], 0),
    ([true, false, false, true, true, false, false, true, false, true, true, true],
      [true, false, false, true, false, true, false, false, false, true, true, false], 2),
    ([true, false, false, true, false, false, false, true, false, true, false, false],
      [true, false, false, true, true, false, false, true, false, true, true, true], 0),
    ([true, false, false, true, false, false, false, true, true, true, false, false],
      [true, false, false, true, false, false, false, true, false, true, false, false], 11),
    ([true, false, false, true, true, false, false, true, true, true, true, true],
      [true, false, false, true, false, false, false, true, true, true, false, false], 0),
    ([true, false, false, true, true, true, false, false, true, true, false, false],
      [true, false, false, true, false, false, false, true, false, true, false, false], 2),
    ([true, false, false, true, false, true, false, false, true, true, false, true],
      [true, false, false, true, true, true, false, false, true, true, false, false], 0),
    ([true, false, false, true, false, true, false, false, false, true, false, true],
      [true, false, false, true, false, true, false, false, true, true, false, true], 10),
    ([true, false, false, true, true, true, false, false, false, true, false, false],
      [true, false, false, true, false, true, false, false, false, true, false, true], 0),
    ([true, false, false, true, false, false, false, true, true, true, true, false],
      [true, false, false, true, false, false, false, true, false, true, false, false], 9),
    ([true, false, false, true, true, false, false, true, true, true, false, true],
      [true, false, false, true, false, false, false, true, true, true, true, false], 0),
    ([true, false, false, true, false, false, false, true, false, true, true, false],
      [true, false, false, true, false, false, false, true, true, true, true, false], 11),
    ([true, false, false, true, true, false, false, true, false, true, false, true],
      [true, false, false, true, false, false, false, true, false, true, true, false], 0),
    ([true, false, false, true, true, true, true, false, true, true, true, false],
      [true, false, false, true, false, false, false, true, false, true, true, false], 2),
    ([true, false, false, true, false, true, true, false, false, true, true, true],
      [true, false, false, true, true, true, true, false, true, true, true, false], 0),
    ([true, false, false, true, false, true, true, false, true, true, true, true],
      [true, false, false, true, false, true, true, false, false, true, true, true], 10),
    ([true, false, false, true, true, true, true, false, false, true, true, false],
      [true, false, false, true, false, true, true, false, true, true, true, true], 0),
    ([true, false, false, true, true, false, true, true, false, true, true, false],
      [true, false, false, true, false, true, true, false, false, true, true, true], 2),
    ([true, false, false, true, false, false, true, true, true, true, false, true],
      [true, false, false, true, true, false, true, true, false, true, true, false], 0),
    ([true, false, false, true, false, false, true, true, false, true, false, true],
      [true, false, false, true, false, false, true, true, true, true, false, true], 11),
    ([true, false, false, true, true, false, true, true, true, true, true, false],
      [true, false, false, true, false, false, true, true, false, true, false, true], 0),
    ([true, false, false, true, true, true, true, false, true, true, false, true],
      [true, false, false, true, false, false, true, true, false, true, false, true], 2),
    ([true, false, false, true, false, true, true, false, false, true, false, false],
      [true, false, false, true, true, true, true, false, true, true, false, true], 0),
    ([true, false, false, true, false, true, true, false, true, true, false, false],
      [true, false, false, true, false, true, true, false, false, true, false, false], 10),
    ([true, false, false, true, true, true, true, false, false, true, false, true],
      [true, false, false, true, false, true, true, false, true, true, false, false], 0),
    ([true, false, false, false, true, false, false, false, true, false, false, true],
      [true, false, false, true, false, true, false, false, false, true, false, true], 1),
    ([true, false, false, false, false, true, false, true, false, true, true, false],
      [true, false, false, false, true, false, false, false, true, false, false, true], 2),
    ([true, false, false, false, false, true, false, true, false, true, true, true],
      [true, false, false, false, false, true, false, true, false, true, true, false], 0),
    ([true, false, false, false, false, true, false, true, true, true, true, false],
      [true, false, false, false, false, true, false, true, false, true, true, false], 10),
    ([true, false, false, false, false, true, false, true, true, true, true, true],
      [true, false, false, false, false, true, false, true, true, true, true, false], 0),
    ([true, false, false, false, true, false, false, false, true, false, false, false],
      [true, false, false, false, false, true, false, true, false, true, true, true], 2),
    ([true, false, false, false, true, false, false, false, false, false, false, true],
      [true, false, false, false, false, true, false, true, true, true, true, false], 2),
    ([true, false, false, false, true, false, false, false, false, false, false, false],
      [true, false, false, false, false, true, false, true, true, true, true, true], 2),
    ([true, false, false, false, false, true, true, true, true, true, false, true],
      [true, false, false, false, false, true, false, true, false, true, true, false], 9),
    ([true, false, false, false, false, true, true, true, false, true, false, false],
      [true, false, false, false, false, true, true, true, true, true, false, true], 0),
    ([true, false, false, false, false, true, true, true, true, true, false, false],
      [true, false, false, false, false, true, true, true, false, true, false, false], 10),
    ([true, false, false, false, false, true, true, true, false, true, false, true],
      [true, false, false, false, false, true, true, true, true, true, false, false], 0),
    ([true, false, false, false, true, false, false, false, true, false, true, true],
      [true, false, false, false, false, true, true, true, false, true, false, false], 2),
    ([true, false, false, false, true, false, false, false, true, false, true, false],
      [true, false, false, false, false, true, true, true, false, true, false, true], 2),
    ([true, false, false, false, true, false, false, false, false, false, true, true],
      [true, false, false, false, false, true, true, true, true, true, false, false], 2),
    ([true, false, false, false, true, false, false, false, false, false, true, false],
      [true, false, false, false, false, true, true, true, true, true, false, true], 2),
    ([false, false, false, false, true, false, false, false, false, false, false, false],
      [false, false, false, false, false, false, true, false, false, false, false, false], 13),
    ([false, false, false, false, true, false, true, false, true, false, false, true],
      [false, false, false, false, true, false, false, false, false, false, false, false], 2),
    ([false, false, false, false, true, false, true, false, false, false, false, true],
      [false, false, false, false, true, false, true, false, true, false, false, true], 0),
    ([false, false, false, false, true, false, false, false, true, false, false, false],
      [false, false, false, false, true, false, true, false, false, false, false, true], 2),
    ([false, false, false, false, true, false, true, false, true, false, true, false],
      [false, false, false, false, true, false, false, false, false, false, false, false], 1),
    ([false, false, false, false, true, false, true, false, false, false, true, false],
      [false, false, false, false, true, false, true, false, true, false, true, false], 0),
    ([false, false, false, false, true, false, true, false, true, false, true, true],
      [false, false, false, false, true, false, true, false, false, false, true, false], 2),
    ([false, false, false, false, true, false, true, false, false, false, true, true],
      [false, false, false, false, true, false, true, false, true, false, true, true], 0),
    ([false, false, true, false, false, false, false, false, false, false, false, false],
      [false, false, false, false, true, false, false, false, false, false, false, false], 12),
    ([false, false, true, false, true, true, true, true, false, true, true, true],
      [false, false, true, false, false, false, false, false, false, false, false, false], 0),
    ([false, false, true, false, false, false, true, false, false, false, false, false],
      [false, false, true, false, false, false, false, false, false, false, false, false], 10),
    ([false, false, true, false, true, true, false, true, true, true, true, true],
      [false, false, true, false, false, false, true, false, false, false, false, false], 0),
    ([false, false, true, false, true, true, false, true, false, true, true, false],
      [false, false, true, false, true, true, false, true, true, true, true, true], 2),
    ([false, false, true, false, false, false, true, false, true, false, false, true],
      [false, false, true, false, true, true, false, true, false, true, true, false], 0),
    ([false, false, true, false, false, false, false, false, true, false, false, true],
      [false, false, true, false, false, false, true, false, true, false, false, true], 10),
    ([false, false, true, false, true, true, true, true, true, true, true, false],
      [false, false, true, false, false, false, false, false, true, false, false, true], 0),
    ([false, false, true, false, true, true, true, true, true, false, false, true],
      [false, false, true, false, true, true, false, true, false, true, true, false], 1),
    ([false, false, true, false, false, false, false, false, true, true, false, true],
      [false, false, true, false, true, true, true, true, true, false, false, true], 0),
    ([false, false, true, false, false, false, true, false, true, true, false, true],
      [false, false, true, false, false, false, false, false, true, true, false, true], 10),
    ([false, false, true, false, true, true, false, true, false, false, false, true],
      [false, false, true, false, false, false, true, false, true, true, false, true], 0),
    ([false, false, true, false, true, true, true, true, true, false, false, false],
      [false, false, true, false, true, true, false, true, false, false, false, true], 2),
    ([false, false, true, false, false, false, false, false, true, true, false, false],
      [false, false, true, false, true, true, true, true, true, false, false, false], 0),
    ([false, false, true, false, false, false, true, false, true, true, false, false],
      [false, false, true, false, false, false, false, false, true, true, false, false], 10),
    ([false, false, true, false, true, true, false, true, false, false, false, false],
      [false, false, true, false, false, false, true, false, true, true, false, false], 0),
    ([false, false, false, false, true, false, false, false, false, false, true, false],
      [false, false, false, false, false, false, true, false, false, false, false, true], 13),
    ([false, false, false, false, true, false, false, false, true, false, true, true],
      [false, false, false, false, true, false, false, false, false, false, true, false], 2),
    ([false, false, false, false, true, false, false, false, true, false, true, false],
      [false, false, false, false, true, false, false, false, false, false, true, false], 9),
    ([false, false, false, false, true, false, false, false, false, false, true, true],
      [false, false, false, false, true, false, false, false, true, false, true, false], 2),
    ([false, false, false, false, true, false, false, false, false, false, false, true],
      [false, false, false, false, true, false, false, false, false, false, true, false], 1),
    ([false, false, false, false, true, false, true, false, true, false, false, false],
      [false, false, false, false, true, false, false, false, false, false, false, true], 2),
    ([false, false, false, false, true, false, true, false, false, false, false, false],
      [false, false, false, false, true, false, true, false, true, false, false, false], 0),
    ([false, false, false, false, true, false, false, false, true, false, false, true],
      [false, false, false, false, true, false, true, false, false, false, false, false], 2),
    ([false, false, true, false, false, false, false, false, false, false, false, true],
      [false, false, false, false, true, false, false, false, false, false, false, true], 12),
    ([false, false, true, false, true, true, true, true, false, true, true, false],
      [false, false, true, false, false, false, false, false, false, false, false, true], 0),
    ([false, false, true, false, false, false, true, false, false, false, false, true],
      [false, false, true, false, false, false, false, false, false, false, false, true], 10),
    ([false, false, true, false, true, true, false, true, true, true, true, false],
      [false, false, true, false, false, false, true, false, false, false, false, true], 0),
    ([false, false, true, false, true, true, false, true, false, true, true, true],
      [false, false, true, false, true, true, false, true, true, true, true, false], 2),
    ([false, false, true, false, false, false, true, false, true, false, false, false],
      [false, false, true, false, true, true, false, true, false, true, true, true], 0),
    ([false, false, true, false, false, false, false, false, true, false, false, false],
      [false, false, true, false, false, false, true, false, true, false, false, false], 10),
    ([false, false, true, false, true, true, true, true, true, true, true, true],
      [false, false, true, false, false, false, false, false, true, false, false, false], 0),
    ([false, false, true, false, true, true, false, true, true, false, false, false],
      [false, false, true, false, true, true, false, true, false, true, true, true], 1),
    ([false, false, true, false, false, false, true, false, false, true, false, false],
      [false, false, true, false, true, true, false, true, true, false, false, false], 0),
    ([false, false, true, false, false, false, false, false, false, true, false, false],
      [false, false, true, false, false, false, true, false, false, true, false, false], 10),
    ([false, false, true, false, true, true, true, true, false, false, false, false],
      [false, false, true, false, false, false, false, false, false, true, false, false], 0),
    ([false, false, true, false, true, true, true, true, false, false, false, true],
      [false, false, true, false, true, true, false, true, true, false, false, false], 2),
    ([false, false, true, false, false, false, false, false, false, true, false, true],
      [false, false, true, false, true, true, true, true, false, false, false, true], 0),
    ([false, false, true, false, false, false, true, false, false, true, false, true],
      [false, false, true, false, false, false, false, false, false, true, false, true], 10),
    ([false, false, true, false, true, true, false, true, true, false, false, true],
      [false, false, true, false, false, false, true, false, false, true, false, true], 0)]

end CFSG.RankThree.PartOne.SEITZRF.FusTwo
