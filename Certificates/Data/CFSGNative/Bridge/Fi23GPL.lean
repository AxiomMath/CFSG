module

public import Certificates.Data.CFSGNative.Fi23.Certificate

public section

namespace CFSG.Sporadic.Bridge.Fi23GPL.Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def powWord (w : List (Nat × Bool)) (n : Nat) : List (Nat × Bool) :=
  (List.replicate n w).flatten

@[expose] def rels (_ : Unit := ()) : List (List (Nat × Bool)) :=
  let squareWords := (List.range 10).map fun k => [(k, true), (k, true)]
  let edgePairs : List (Nat × Nat) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)]
  let edgeWords := edgePairs.map fun (r, s) => powWord [(r, true), (s, true)] 3
  let nonedgePairs : List (Nat × Nat) :=
    [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9),
      (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9),
      (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9),
      (3, 5), (3, 6), (3, 8), (3, 9),
      (4, 6), (4, 7), (4, 8), (4, 9),
      (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (7, 9), (8, 9)]
  let nonedgeWords := nonedgePairs.map fun (r, s) => powWord [(r, true), (s, true)] 2
  squareWords ++ edgeWords ++ nonedgeWords ++
    [powWord [(3, true), (2, true), (1, true), (3, true), (4, true), (5, true),
        (3, true), (7, true), (8, true)] 10,
      powWord [(0, true), (1, true), (2, true), (3, true), (4, true), (5, true),
        (7, true)] 9]

@[expose] def imgText : String := include_str "Fi23GPLImages.txt"

@[expose] def surjText : String := include_str "Fi23GPLSurj.txt"

@[expose] def parseLine (s : String) : List Int :=
  (s.splitOn " ").filterMap String.toInt?

@[expose] def parseWords (s : String) : Array (List Int) :=
  (((s.splitOn "\n").filter fun l => !l.isEmpty).map parseLine).toArray

@[expose] def imgWords (_ : Unit := ()) : Array (List Int) := parseWords imgText

@[expose] def surjWords (_ : Unit := ()) : Array (List Int) := parseWords surjText

@[expose] def letterOf (l : Nat × Bool) : Int := if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

@[expose] def imgLetter (I Iv : Array Table) (z : Int) : Table :=
  if 0 < z then I[(z - 1).toNat]! else Iv[(-z - 1).toNat]!

@[expose] def seedLetter (G4 : Array Table) (z : Int) : Table :=
  if z = 1 then G4[0]! else if z = -1 then G4[1]! else if z = 2 then G4[2]! else G4[3]!

@[noinline, expose] def imageChecks (α β : Table) (I Iv : Array Table) : Bool :=
  imgWords.size == 10 && surjWords.size == 2 &&
    surjWords.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ 10)) &&
    (List.range 10).all (fun k => invOK 31671 I[k]! Iv[k]!) &&
    rels.all (fun r =>
      tupleEq (apT (wordT 31671 (imgLetter I Iv) (r.map letterOf)) chainQ) chainQ) &&
    tupleEq (apT (wordT 31671 (imgLetter I Iv) surjWords[0]!) chainQ) (apT α chainQ) &&
    tupleEq (apT (wordT 31671 (imgLetter I Iv) surjWords[1]!) chainQ) (apT β chainQ)

@[noinline, expose] def inverseChecks (α β : Table) (I : Array Table) : Bool :=
  imageChecks α β I (I.map (invT 31671))

@[noinline, expose] def tableChecks (α β : Table) (G4 : Array Table) : Bool :=
  inverseChecks α β (imgWords.map (wordT 31671 (seedLetter G4)))

@[noinline, expose] def seedChecks (α β αi βi : Table) : Bool :=
  invOK 31671 α αi && invOK 31671 β βi && tableChecks α β #[α, αi, β, βi]

@[expose] def bridgeCheck (_ : Unit) : Bool :=
  let O := orbitData ()
  seedChecks O.alpha O.beta O.alpha (invT 31671 O.beta)

end CFSG.Sporadic.Bridge.Fi23GPL.Native
