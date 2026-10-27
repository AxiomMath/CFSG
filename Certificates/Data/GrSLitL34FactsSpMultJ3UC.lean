module

public import Certificates.Data.GrSLitL34FactsSpMultJ3Check

public section

namespace CFSG.ComponentClassification.GSThmB.SpMult

@[expose] def altWord (es : List Bool) : List (Fin 2 × Bool) :=
  es.flatMap fun e => [(0, true), (1, e)]

@[expose] def powW {m : ℕ} (w : List (Fin m × Bool)) (n : ℕ) : List (Fin m × Bool) :=
  (List.replicate n w).flatten

@[expose] def dblOdd (o : ℕ) : ℕ := if o % 2 = 0 then o else 2 * o

@[expose] def ucC : List (Fin 2 × Bool) :=
  powW [(1, true), (0, true)] 5 ++ [(1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def ucU : List (Fin 2 × Bool) := FreeGroup.invRev (powW ((0, true) :: ucC) 4)

@[expose] def j3ExtraData : List (List Bool × ℕ) :=
  [([true, true, true, true, false, true, false], 4),
   ([true, false, true, false, false, false, false], 4),
   ([true, false], 9),
   ([true, false, true, false, true, false], 3),
   ([true], 19),
   ([false], 19),
   ([true, true, true, true, false], 8),
   ([true, true, false, true, false], 8),
   ([true, false, true, false, false], 8),
   ([true, false, false, false, false], 8),
   ([true, true, true, true, true, true, true, false], 6),
   ([true, true, true, false, true, false, true, false], 6)]

@[expose] def j3Extra : List (List (Fin 2 × Bool)) :=
  j3ExtraData.map fun p => powW (altWord p.1) (dblOdd p.2)

@[expose] def toFin2 {m : ℕ} (w : List (Fin m × Bool)) : List (Fin 2 × Bool) :=
  w.map fun l => (Fin.ofNat 2 l.1.val, l.2)

@[expose] def ucRels : List (List (Fin 2 × Bool)) := j3CoverRels.map toFin2 ++ j3Extra

@[expose] def ucUe : CFSG.CosetTable.PG 2 ucRels := PresentedGroup.mk _ (FreeGroup.mk ucU)

@[expose] def ucCe : CFSG.CosetTable.PG 2 ucRels := PresentedGroup.mk _ (FreeGroup.mk ucC)

@[expose] def ucABWords : List (List (Fin 2 × Bool)) :=
  powW ((0, true) :: ucC) 6 :: j3ExtraData.map fun p => powW (altWord p.1) p.2

@[expose] def gammaPowData : List (List (Fin 2 × Bool) × ℕ) :=
  [([(0, true), (1, true)], 10),
   ([(0, true), (1, false)], 4),
   ([(0, false), (1, true), (1, true)], 15),
   ([(0, true), (1, true), (0, false), (1, true)], 15),
   ([(0, true), (1, true), (1, true)], 15)]

@[expose] def gammaH : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true), (0, true)],
   [(1, true), (1, true), (1, true), (1, true)],
   [(0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true)],
   [(0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, false),
    (1, true), (0, true), (1, true), (0, true), (1, false), (1, false)],
   [(0, false), (1, false), (1, false), (0, true), (1, true), (0, false), (1, false), (1, false),
    (0, false), (1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false),
    (1, false)]]

@[expose] def gammaRels : List (List (Fin 2 × Bool)) :=
  [powW [(0, true)] 3, powW [(1, true)] 4] ++
    gammaPowData.map (fun p => powW p.1 (dblOdd p.2)) ++ gammaH.flatMap centralWords

@[expose] def gammaJ3Words : List (List (Fin 2 × Bool)) :=
  [powW [(0, true)] 3, powW [(1, true)] 4] ++ gammaPowData.map (fun p => powW p.1 p.2) ++ gammaH

end CFSG.ComponentClassification.GSThmB.SpMult
