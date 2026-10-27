module

public import Certificates.Data.CoverCenterThreeCover
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Certificates.CosetTableCompactPresented

public section

namespace CFSG.SectionRank.Native

open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.CosetTable

@[expose] def j3CoverProg : List Op := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 5, .mul 2 5 6, .mul 3 3 7, .mul 3 7 8,
      .mul 8 8 9, .pow 18 9 10, .mul 10 6 11, .mul 11 9 12, .mul 2 2 13, .mul 13 13 14,
      .mul 14 14 15, .mul 2 15 16, .pow 18 16 17, .mul 17 0 18, .mul 18 16 19, .mul 19 12 20,
      .mul 20 12 21, .mul 21 12 22, .mul 22 12 23, .mul 12 19 24, .mul 24 12 25, .mul 25 12 26,
      .mul 26 12 27, .mul 19 12 28, .mul 28 19 29, .mul 29 12 30, .mul 30 19 31, .mul 31 12 32,
      .mul 32 12 33, .mul 33 12 34, .mul 34 12 35, .mul 35 19 36, .mul 36 12 37, .mul 37 12 38,
      .mul 19 12 39, .mul 39 12 40, .mul 40 12 41, .mul 41 12 42, .mul 42 19 43, .mul 43 12 44,
      .mul 44 12 45, .mul 45 12 46, .mul 46 12 47, .mul 47 19 48, .mul 48 12 49, .mul 49 12 50,
      .mul 50 12 51, .mul 51 12 52, .mul 12 19 53, .mul 53 12 54, .mul 54 12 55, .mul 55 12 56,
      .mul 56 12 57, .mul 57 19 58, .mul 58 12 59, .mul 59 12 60, .mul 60 12 61, .mul 61 12 62,
      .mul 62 19 63, .mul 63 12 64, .mul 64 12 65, .mul 65 12 66
  ]

@[expose] def j3CoverRels : List (List (Fin 6 × Bool)) := [
    [(1, true), (1, true), (1, true), (4, false)],
    [(2, true), (2, true), (2, true), (5, false)],
    [(3, true), (3, true), (3, true)],
    [(4, true), (4, true), (4, true)],
    [(5, true), (5, true), (5, true)],
    [(2, true), (1, true), (4, false), (4, false), (3, false), (3, false), (2, false), (1, false)],
    [(3, true), (1, true), (5, false), (4, false), (3, false), (1, false)],
    [(4, true), (1, true), (4, false), (1, false)],
    [(5, true), (1, true), (5, false), (1, false)],
    [(3, true), (2, true), (5, false), (4, false), (4, false), (3, false), (2, false)],
    [(4, true), (2, true), (4, false), (2, false)],
    [(5, true), (2, true), (5, false), (2, false)],
    [(4, true), (3, true), (4, false), (3, false)],
    [(5, true), (3, true), (5, false), (3, false)],
    [(5, true), (4, true), (5, false), (4, false)],
    [(0, true), (1, false), (0, false), (2, true)],
    [(0, true), (2, false), (0, false), (1, true), (2, true), (2, true), (3, true), (3, true),
      (4, true), (4, true)],
    [(0, true), (3, false), (0, false), (3, true), (3, true), (5, true)],
    [(0, true), (4, false), (0, false), (5, true)],
    [(0, true), (5, false), (0, false), (4, true), (5, true)]
  ]

@[expose] def j3CoverCW : List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) := [
    ([], []),
    ([(0, true)], [(1, true), (2, true), (2, true), (4, true)]),
    ([(0, true)], [(1, true), (1, true), (2, true), (2, true), (4, true)]),
    ([(0, true)], [(3, true), (4, true), (4, true), (5, true), (5, true)]),
    ([(0, true)], [(5, true)]),
    ([(0, true)], [(4, true), (5, true)])
  ]

@[expose] def j3CoverE (i : Fin 6) : Nat := if i.val = 0 then 8 else 0

@[expose] def j3CoverCWf (i : Fin 6) : List (Fin 6 × Bool) × List (Fin 6 × Bool) :=
  j3CoverCW.getD i.val ([], [])

@[expose] def j3CoverData : CoverData 6 where
  seedA := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m2"
  nregs := 67
  prog := j3CoverProg
  gens := [12, 23, 27, 38, 52, 66]
  invExp := [8, 9, 9, 9, 9, 9]
  e := j3CoverE
  cw := j3CoverCWf
  rels := j3CoverRels

@[expose] def j3GammaWords : List (List (Fin 6 × Bool)) :=
  gammaWords j3CoverE j3CoverCWf j3CoverRels

end CFSG.SectionRank.Native
