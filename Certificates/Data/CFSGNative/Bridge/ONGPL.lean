module

public import Certificates.Data.CFSGNative.ON.Certificate

public section

namespace CFSG.Sporadic.Bridge.ONGPL.Native

open CFSG.Sporadic.ON.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def rels (_ : Unit := ()) : List (List (Nat × Bool)) := [
    [(0, true), (0, true)],
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(4, true), (4, true)],
    [(5, true), (5, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
    [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true),
      (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
    [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, true), (3, true), (0, true), (3, true)],
    [(0, true), (4, true), (0, true), (4, true)],
    [(0, true), (5, true), (0, true), (5, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(1, true), (4, true), (1, true), (4, true)],
    [(1, true), (5, true), (1, true), (5, true)],
    [(2, true), (4, true), (2, true), (4, true)],
    [(2, true), (5, true), (2, true), (5, true)],
    [(3, true), (5, true), (3, true), (5, true)],
    [(6, true), (6, true), (6, true), (6, true)],
    [(5, false), (0, false), (6, true), (6, true)],
    [(5, false), (0, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true),
      (2, true), (3, true)],
    [(2, true), (6, false), (3, false), (6, false), (3, false), (2, true), (3, true), (6, true),
      (3, true), (6, true)],
    [(3, true), (6, false), (2, false), (6, false), (2, false), (3, true), (2, true), (6, true),
      (2, true), (6, true)],
    [(1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true), (6, true),
      (1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true), (6, true),
      (1, true), (2, true), (3, true), (6, true)],
    [(6, true), (1, true), (2, false), (6, true), (2, true), (1, false), (6, true), (1, true),
      (2, false), (6, true), (2, true)],
    [(6, true), (4, true), (3, false), (6, true), (3, true), (4, false), (6, true), (4, true),
      (3, false), (6, true), (3, true)]]

@[expose] def imgText : String := include_str "ONGPLImages.txt"

@[expose] def surjText : String := include_str "ONGPLSurj.txt"

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
  imgWords.size == 7 && surjWords.size == 2 &&
    surjWords.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ 7)) &&
    (List.range 7).all (fun k => invOK nPts I[k]! Iv[k]!) &&
    rels.all (fun r =>
      tupleEq (apT (wordT nPts (imgLetter I Iv) (r.map letterOf)) chainQ) chainQ) &&
    tupleEq (apT (wordT nPts (imgLetter I Iv) surjWords[0]!) chainQ) (apT α chainQ) &&
    tupleEq (apT (wordT nPts (imgLetter I Iv) surjWords[1]!) chainQ) (apT β chainQ)

@[noinline, expose] def inverseChecks (α β : Table) (I : Array Table) : Bool :=
  imageChecks α β I (I.map (invT nPts))

@[noinline, expose] def tableChecks (α β : Table) (G4 : Array Table) : Bool :=
  inverseChecks α β (imgWords.map (wordT nPts (seedLetter G4)))

@[noinline, expose] def seedChecks (α β αi βi : Table) : Bool :=
  invOK nPts α αi && invOK nPts β βi && tableChecks α β #[α, αi, β, βi]

@[expose] def bridgeCheck (_ : Unit) : Bool :=
  let O := orbitData ()
  seedChecks O.alpha O.beta (invT nPts O.alpha) (invT nPts O.beta)

end CFSG.Sporadic.Bridge.ONGPL.Native
