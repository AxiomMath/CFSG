module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last.K135

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def regA0 : Nat := 29

@[expose] def regA1 : Nat := 32

@[expose] def regA2 : Nat := 34

@[expose] def regX : Nat := 24

@[expose] def onProg : List Op := [
    .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 4 6, .mul 2 6 7, .mul 7 7 8,
    .mul 8 8 9, .mul 3 3 10, .mul 10 10 11, .pow 18 11 12, .mul 12 9 13, .mul 13 11 14,
    .mul 2 2 15, .mul 15 15 16, .pow 10 16 17, .mul 17 0 18, .mul 18 16 19, .pow 2 14 20,
    .mul 20 14 21, .pow 2 14 22, .mul 21 22 23, .mul 23 19 24, .mul 14 19 25, .pow 2 14 26,
    .mul 25 26 27, .mul 27 19 28, .pow 4 28 29, .pow 6 24 30, .mul 24 29 31, .mul 31 30 32,
    .mul 24 32 33, .mul 33 30 34]

@[expose] def wA (i j k : Nat) : Word := [(regA0, i), (regA1, j), (regA2, k)]

@[expose] def invTriples : List (Nat × Nat × Nat) :=
  [(0, 0, 2), (0, 2, 0), (0, 2, 2), (2, 0, 0), (2, 0, 2), (2, 2, 0), (2, 2, 2)]

@[expose] def conjX (w : Word) : Word := [(regX, 1)] ++ w ++ [(regX, 6)]

@[expose] def onFacts : List MFact :=
  [.ord regA0 4, .ord regA1 4, .ord regA2 4, .ord regX 7,
    .eq [(regA0, 1), (regA1, 1)] [(regA1, 1), (regA0, 1)],
    .eq [(regA0, 1), (regA2, 1)] [(regA2, 1), (regA0, 1)],
    .eq [(regA1, 1), (regA2, 1)] [(regA2, 1), (regA1, 1)],
    .ne [(regX, 1)] [] 0,
    .conj regX [(regA0, 1)] (wA 0 1 0),
    .conj regX [(regA1, 1)] (wA 0 0 1),
    .conj regX [(regA2, 1)] (wA 1 2 1)] ++
  invTriples.map (fun p => .ne (wA p.1 p.2.1 p.2.2) [] 0) ++
  invTriples.map (fun p => .ne (conjX (wA p.1 p.2.1 p.2.2)) (wA p.1 p.2.1 p.2.2) 0)

@[expose] def onCert : MCert where
  nregs := 35
  prog := onProg
  facts := onFacts

end CFSG.RankThree.PartTwo.Sec13.F135Last.K135
