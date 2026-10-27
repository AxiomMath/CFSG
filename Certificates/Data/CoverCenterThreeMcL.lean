module

public import Certificates.Data.CoverCenterThreeCover
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.SectionRank.Native

open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.CosetTable

@[expose] def mclCoverProg : List Op := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 3 0, .mul 2 3 4, .mul 4 1 5, .mul 5 3 1, .mul 3 3 4,
      .mul 4 4 3, .pow 2 3 4, .mul 4 1 5, .mul 5 3 1, .mul 2 2 3, .mul 3 3 2, .mul 2 2 3,
      .pow 10 3 4, .mul 4 0 5, .mul 5 3 0, .mul 1 0 6, .mul 6 1 7, .mul 7 0 8, .mul 8 1 9,
      .mul 9 1 10, .mul 10 0 11, .mul 11 0 12, .mul 12 1 13, .mul 13 0 14, .mul 14 0 15,
      .mul 15 1 16, .mul 16 0 17, .mul 17 1 18, .mul 18 0 19, .mul 1 1 20, .mul 20 0 21,
      .mul 21 0 22, .mul 22 1 23, .mul 23 1 24, .mul 24 1 25, .mul 25 1 26, .mul 26 0 27,
      .mul 27 0 28, .mul 28 1 29, .mul 29 1 30, .mul 30 1 31, .mul 31 0 32, .mul 32 0 33,
      .mul 33 1 34, .mul 0 0 35, .mul 35 0 36, .mul 36 1 37, .mul 37 1 38, .mul 38 1 39,
      .mul 39 1 40, .mul 0 0 41, .mul 41 1 42, .mul 42 1 43, .mul 43 1 44, .mul 44 1 45,
      .mul 45 0 46, .mul 1 0 47, .mul 47 0 48, .mul 48 0 49, .mul 49 1 50, .mul 50 1 51,
      .mul 51 1 52, .mul 1 1 53, .mul 53 0 54, .mul 54 0 55, .mul 55 0 56, .mul 56 1 57,
      .mul 57 1 58, .mul 0 1 59, .mul 59 1 60, .mul 60 0 61, .mul 61 1 62, .mul 62 1 63,
      .mul 63 0 64, .mul 64 1 65, .mul 65 1 66, .mul 66 0 67, .mul 67 1 68, .mul 68 1 69,
      .mul 69 0 70, .mul 70 1 71, .mul 71 1 72
  ]

@[expose] def mclCoverRels : List (List (Fin 7 × Bool)) := [
    [(2, true), (2, true), (2, true)],
    [(3, true), (3, true), (3, true)],
    [(4, true), (4, true), (4, true)],
    [(5, true), (5, true), (5, true)],
    [(6, true), (6, true), (6, true)],
    [(3, true), (2, true), (6, false), (3, false), (2, false)],
    [(4, true), (2, true), (6, false), (4, false), (2, false)],
    [(5, true), (2, true), (5, false), (2, false)],
    [(6, true), (2, true), (6, false), (2, false)],
    [(4, true), (3, true), (4, false), (3, false)],
    [(5, true), (3, true), (6, false), (5, false), (3, false)],
    [(6, true), (3, true), (6, false), (3, false)],
    [(5, true), (4, true), (6, false), (6, false), (5, false), (4, false)],
    [(6, true), (4, true), (6, false), (4, false)],
    [(6, true), (5, true), (6, false), (5, false)],
    [(0, true), (2, true), (0, false), (6, false), (5, false), (5, false), (4, false),
     (3, false), (3, false), (2, false), (2, false)],
    [(0, true), (3, true), (0, false), (6, false), (5, false), (5, false), (2, false), (2, false)],
    [(0, true), (4, true), (0, false), (5, false), (5, false), (3, false), (2, false)],
    [(0, true), (5, true), (0, false), (6, false), (5, false), (4, false), (4, false),
     (3, false), (3, false), (2, false)],
    [(0, true), (6, true), (0, false), (6, false), (6, false)],
    [(1, true), (2, true), (1, false), (6, false), (6, false), (5, false), (4, false), (2, false)],
    [(1, true), (3, true), (1, false), (6, false), (5, false), (5, false)],
    [(1, true), (4, true), (1, false), (6, false), (6, false), (4, false), (3, false), (2, false)],
    [(1, true), (5, true), (1, false), (6, false), (6, false), (5, false), (5, false),
     (3, false), (2, false)],
    [(1, true), (6, true), (1, false), (6, false)],
    [(0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true),
     (0, true), (1, false), (0, false), (6, false), (6, false), (4, false), (4, false),
     (2, false), (2, false)],
    [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
     (0, false), (1, true), (1, true), (0, false), (6, false), (5, false), (4, false),
     (3, false), (2, false)],
    [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
     (0, true), (1, false), (0, false), (1, false), (2, false), (2, false)]
  ]

@[expose] def mclCoverCW : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) := [
    ([], []),
    ([(0, false), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false),
      (0, false), (1, false), (0, true), (0, true)],
     [(0, false), (1, false), (0, false), (1, false), (0, true), (1, false), (1, false),
      (1, false), (0, true)]),
    ([(0, true)], [(3, true), (3, true), (4, true), (5, true), (5, true), (6, true)]),
    ([(0, true)], [(2, true), (2, true), (3, true), (5, true), (5, true)]),
    ([(0, true)], [(2, true), (3, true), (4, true), (5, true), (5, true), (6, true), (6, true)]),
    ([(0, true)],
     [(2, true), (3, true), (3, true), (4, true), (4, true), (5, true), (5, true), (6, true),
      (6, true)]),
    ([(0, true)], [(6, true)])
  ]

@[expose] def mclCoverE (i : Fin 7) : Nat := if i.val = 0 then 4 else 0

@[expose] def mclCoverCWf (i : Fin 7) : List (Fin 7 × Bool) × List (Fin 7 × Bool) :=
  mclCoverCW.getD i.val ([], [])

@[expose] def mclCoverData : CoverData 7 where
  seedA := include_str "../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 73
  prog := mclCoverProg
  gens := [19, 34, 40, 46, 52, 58, 72]
  invExp := [4, 10, 3, 3, 3, 3, 3]
  e := mclCoverE
  cw := mclCoverCWf
  rels := mclCoverRels

@[expose] def mclGammaWords : List (List (Fin 7 × Bool)) :=
  gammaWords mclCoverE mclCoverCWf mclCoverRels

@[expose] def mclPresWords : List (List (Fin 7 × Bool)) :=
  mclCoverRels ++ [List.replicate 4 (0, true)] ++
    (List.finRange 6).map fun i =>
      commW (mclCoverCWf i.succ).1 (mclCoverCWf i.succ).2 ++ [(i.succ, false)]

@[expose] def f3Key (d : Nat) (v : CFSG.F3.Native.V) : Nat :=
  (List.range d).foldr (fun j acc => v.get j + 3 * acc) 0

end CFSG.SectionRank.Native
