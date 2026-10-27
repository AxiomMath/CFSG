module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4UFacts
public import CFSG.RankThree.PartTwo.Sec21.FF84S34Dec
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000


@[expose] def rep4 : P8 := pc * pa

theorem rep4_tab : FF84.tab rep4 = [1, 0, 7, 4, 3, 6, 5, 2] := by decide +kernel

set_option maxHeartbeats 8000000 in
@[expose] def rankP1 : List (Perm (Fin 8)) :=
  [(1),
   (swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5),
   (swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 1 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 * swap (2 : Fin 8) 3 * swap (4 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 * swap (2 : Fin 8) 4 * swap (3 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 * swap (2 : Fin 8) 3 * swap (4 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 * swap (2 : Fin 8) 4 * swap (3 : Fin 8) 7),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5)]

@[expose] def rankP1T : List (List (Fin 8)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
   [0, 1, 2, 4, 3, 6, 5, 7],
   [0, 1, 2, 5, 6, 3, 4, 7],
   [0, 1, 2, 6, 5, 4, 3, 7],
   [0, 1, 7, 3, 4, 6, 5, 2],
   [0, 1, 7, 4, 3, 5, 6, 2],
   [0, 1, 7, 5, 6, 4, 3, 2],
   [0, 1, 7, 6, 5, 3, 4, 2],
   [1, 0, 2, 3, 4, 6, 5, 7],
   [1, 0, 2, 4, 3, 5, 6, 7],
   [1, 0, 2, 5, 6, 4, 3, 7],
   [1, 0, 2, 6, 5, 3, 4, 7],
   [1, 0, 7, 3, 4, 5, 6, 2],
   [1, 0, 7, 4, 3, 6, 5, 2],
   [1, 0, 7, 5, 6, 3, 4, 2],
   [1, 0, 7, 6, 5, 4, 3, 2],
   [2, 7, 0, 3, 4, 5, 6, 1],
   [2, 7, 0, 4, 3, 6, 5, 1],
   [2, 7, 0, 5, 6, 3, 4, 1],
   [2, 7, 0, 6, 5, 4, 3, 1],
   [2, 7, 1, 3, 4, 6, 5, 0],
   [2, 7, 1, 4, 3, 5, 6, 0],
   [2, 7, 1, 5, 6, 4, 3, 0],
   [2, 7, 1, 6, 5, 3, 4, 0],
   [3, 4, 5, 0, 1, 2, 7, 6],
   [3, 4, 5, 1, 0, 7, 2, 6],
   [3, 4, 5, 2, 7, 0, 1, 6],
   [3, 4, 5, 7, 2, 1, 0, 6],
   [3, 4, 6, 0, 1, 7, 2, 5],
   [3, 4, 6, 1, 0, 2, 7, 5],
   [3, 4, 6, 2, 7, 1, 0, 5],
   [3, 4, 6, 7, 2, 0, 1, 5],
   [4, 3, 5, 0, 1, 7, 2, 6],
   [4, 3, 5, 1, 0, 2, 7, 6],
   [4, 3, 5, 2, 7, 1, 0, 6],
   [4, 3, 5, 7, 2, 0, 1, 6],
   [4, 3, 6, 0, 1, 2, 7, 5],
   [4, 3, 6, 1, 0, 7, 2, 5],
   [4, 3, 6, 2, 7, 0, 1, 5],
   [4, 3, 6, 7, 2, 1, 0, 5],
   [5, 6, 3, 0, 1, 2, 7, 4],
   [5, 6, 3, 1, 0, 7, 2, 4],
   [5, 6, 3, 2, 7, 0, 1, 4],
   [5, 6, 3, 7, 2, 1, 0, 4],
   [5, 6, 4, 0, 1, 7, 2, 3],
   [5, 6, 4, 1, 0, 2, 7, 3],
   [5, 6, 4, 2, 7, 1, 0, 3],
   [5, 6, 4, 7, 2, 0, 1, 3],
   [6, 5, 3, 0, 1, 7, 2, 4],
   [6, 5, 3, 1, 0, 2, 7, 4],
   [6, 5, 3, 2, 7, 1, 0, 4],
   [6, 5, 3, 7, 2, 0, 1, 4],
   [6, 5, 4, 0, 1, 2, 7, 3],
   [6, 5, 4, 1, 0, 7, 2, 3],
   [6, 5, 4, 2, 7, 0, 1, 3],
   [6, 5, 4, 7, 2, 1, 0, 3],
   [7, 2, 0, 3, 4, 6, 5, 1],
   [7, 2, 0, 4, 3, 5, 6, 1],
   [7, 2, 0, 5, 6, 4, 3, 1],
   [7, 2, 0, 6, 5, 3, 4, 1],
   [7, 2, 1, 3, 4, 5, 6, 0],
   [7, 2, 1, 4, 3, 6, 5, 0],
   [7, 2, 1, 5, 6, 3, 4, 0],
   [7, 2, 1, 6, 5, 4, 3, 0]]



set_option maxHeartbeats 8000000 in
@[expose] def rankP2 : List (Perm (Fin 8)) :=
  [(1),
   (swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 1 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 5 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 * swap (2 : Fin 8) 3 * swap (4 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 * swap (2 : Fin 8) 4 * swap (3 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 * swap (2 : Fin 8) 3 * swap (4 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 * swap (2 : Fin 8) 4 * swap (3 : Fin 8) 7),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7)]

@[expose] def rankP2T : List (List (Fin 8)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
   [0, 1, 2, 4, 3, 6, 5, 7],
   [0, 1, 5, 3, 4, 2, 7, 6],
   [0, 1, 5, 4, 3, 7, 2, 6],
   [0, 1, 6, 3, 4, 7, 2, 5],
   [0, 1, 6, 4, 3, 2, 7, 5],
   [0, 1, 7, 3, 4, 6, 5, 2],
   [0, 1, 7, 4, 3, 5, 6, 2],
   [1, 0, 2, 3, 4, 6, 5, 7],
   [1, 0, 2, 4, 3, 5, 6, 7],
   [1, 0, 5, 3, 4, 7, 2, 6],
   [1, 0, 5, 4, 3, 2, 7, 6],
   [1, 0, 6, 3, 4, 2, 7, 5],
   [1, 0, 6, 4, 3, 7, 2, 5],
   [1, 0, 7, 3, 4, 5, 6, 2],
   [1, 0, 7, 4, 3, 6, 5, 2],
   [2, 7, 0, 5, 6, 3, 4, 1],
   [2, 7, 0, 6, 5, 4, 3, 1],
   [2, 7, 1, 5, 6, 4, 3, 0],
   [2, 7, 1, 6, 5, 3, 4, 0],
   [2, 7, 3, 5, 6, 0, 1, 4],
   [2, 7, 3, 6, 5, 1, 0, 4],
   [2, 7, 4, 5, 6, 1, 0, 3],
   [2, 7, 4, 6, 5, 0, 1, 3],
   [3, 4, 2, 0, 1, 5, 6, 7],
   [3, 4, 2, 1, 0, 6, 5, 7],
   [3, 4, 5, 0, 1, 2, 7, 6],
   [3, 4, 5, 1, 0, 7, 2, 6],
   [3, 4, 6, 0, 1, 7, 2, 5],
   [3, 4, 6, 1, 0, 2, 7, 5],
   [3, 4, 7, 0, 1, 6, 5, 2],
   [3, 4, 7, 1, 0, 5, 6, 2],
   [4, 3, 2, 0, 1, 6, 5, 7],
   [4, 3, 2, 1, 0, 5, 6, 7],
   [4, 3, 5, 0, 1, 7, 2, 6],
   [4, 3, 5, 1, 0, 2, 7, 6],
   [4, 3, 6, 0, 1, 2, 7, 5],
   [4, 3, 6, 1, 0, 7, 2, 5],
   [4, 3, 7, 0, 1, 5, 6, 2],
   [4, 3, 7, 1, 0, 6, 5, 2],
   [5, 6, 0, 2, 7, 3, 4, 1],
   [5, 6, 0, 7, 2, 4, 3, 1],
   [5, 6, 1, 2, 7, 4, 3, 0],
   [5, 6, 1, 7, 2, 3, 4, 0],
   [5, 6, 3, 2, 7, 0, 1, 4],
   [5, 6, 3, 7, 2, 1, 0, 4],
   [5, 6, 4, 2, 7, 1, 0, 3],
   [5, 6, 4, 7, 2, 0, 1, 3],
   [6, 5, 0, 2, 7, 4, 3, 1],
   [6, 5, 0, 7, 2, 3, 4, 1],
   [6, 5, 1, 2, 7, 3, 4, 0],
   [6, 5, 1, 7, 2, 4, 3, 0],
   [6, 5, 3, 2, 7, 1, 0, 4],
   [6, 5, 3, 7, 2, 0, 1, 4],
   [6, 5, 4, 2, 7, 0, 1, 3],
   [6, 5, 4, 7, 2, 1, 0, 3],
   [7, 2, 0, 5, 6, 4, 3, 1],
   [7, 2, 0, 6, 5, 3, 4, 1],
   [7, 2, 1, 5, 6, 3, 4, 0],
   [7, 2, 1, 6, 5, 4, 3, 0],
   [7, 2, 3, 5, 6, 1, 0, 4],
   [7, 2, 3, 6, 5, 0, 1, 4],
   [7, 2, 4, 5, 6, 0, 1, 3],
   [7, 2, 4, 6, 5, 1, 0, 3]]



set_option maxHeartbeats 8000000 in
@[expose] def rankQ : List (Perm (Fin 8)) :=
  [(1),
   (swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (2 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 1 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 1 * swap (3 : Fin 8) 4),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7),
   (swap (0 : Fin 8) 1 * swap (2 : Fin 8) 7 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 2 * swap (1 : Fin 8) 7 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 3 * swap (1 : Fin 8) 4 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 5 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 *
     swap (2 : Fin 8) 6 * swap (3 : Fin 8) 4 * swap (5 : Fin 8) 6 * swap (6 : Fin 8) 7),
   (swap (0 : Fin 8) 4 * swap (1 : Fin 8) 3 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 * swap (2 : Fin 8) 3 * swap (4 : Fin 8) 7),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 5 * swap (1 : Fin 8) 6 * swap (2 : Fin 8) 4 * swap (3 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 * swap (2 : Fin 8) 3 * swap (4 : Fin 8) 7),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 3 * swap (3 : Fin 8) 7 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 *
     swap (2 : Fin 8) 4 * swap (3 : Fin 8) 4 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 6 * swap (1 : Fin 8) 5 * swap (2 : Fin 8) 4 * swap (3 : Fin 8) 7),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 *
     swap (2 : Fin 8) 7 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 5 * swap (4 : Fin 8) 6),
   (swap (0 : Fin 8) 7 * swap (1 : Fin 8) 2 * swap (3 : Fin 8) 6 * swap (4 : Fin 8) 5)]

@[expose] def rankQT : List (List (Fin 8)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
   [0, 1, 2, 4, 3, 6, 5, 7],
   [0, 1, 7, 3, 4, 6, 5, 2],
   [0, 1, 7, 4, 3, 5, 6, 2],
   [1, 0, 2, 3, 4, 6, 5, 7],
   [1, 0, 2, 4, 3, 5, 6, 7],
   [1, 0, 7, 3, 4, 5, 6, 2],
   [1, 0, 7, 4, 3, 6, 5, 2],
   [2, 7, 0, 5, 6, 3, 4, 1],
   [2, 7, 0, 6, 5, 4, 3, 1],
   [2, 7, 1, 5, 6, 4, 3, 0],
   [2, 7, 1, 6, 5, 3, 4, 0],
   [3, 4, 5, 0, 1, 2, 7, 6],
   [3, 4, 5, 1, 0, 7, 2, 6],
   [3, 4, 6, 0, 1, 7, 2, 5],
   [3, 4, 6, 1, 0, 2, 7, 5],
   [4, 3, 5, 0, 1, 7, 2, 6],
   [4, 3, 5, 1, 0, 2, 7, 6],
   [4, 3, 6, 0, 1, 2, 7, 5],
   [4, 3, 6, 1, 0, 7, 2, 5],
   [5, 6, 3, 2, 7, 0, 1, 4],
   [5, 6, 3, 7, 2, 1, 0, 4],
   [5, 6, 4, 2, 7, 1, 0, 3],
   [5, 6, 4, 7, 2, 0, 1, 3],
   [6, 5, 3, 2, 7, 1, 0, 4],
   [6, 5, 3, 7, 2, 0, 1, 4],
   [6, 5, 4, 2, 7, 0, 1, 3],
   [6, 5, 4, 7, 2, 1, 0, 3],
   [7, 2, 0, 5, 6, 4, 3, 1],
   [7, 2, 0, 6, 5, 3, 4, 1],
   [7, 2, 1, 5, 6, 3, 4, 0],
   [7, 2, 1, 6, 5, 4, 3, 0]]



set_option maxHeartbeats 8000000 in
@[expose] def rankG : List (Perm (Fin 8)) :=
  [(swap (1 : Fin 8) 7 * swap (2 : Fin 8) 7 * swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (1),
   (swap (1 : Fin 8) 2 * swap (4 : Fin 8) 5),
   (swap (1 : Fin 8) 7 * swap (2 : Fin 8) 7),
   (swap (1 : Fin 8) 7 * swap (2 : Fin 8) 7 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (1 : Fin 8) 2 * swap (4 : Fin 8) 6),
   (swap (1 : Fin 8) 2 * swap (5 : Fin 8) 6),
   (swap (4 : Fin 8) 5 * swap (5 : Fin 8) 6),
   (swap (4 : Fin 8) 6 * swap (5 : Fin 8) 6),
   (swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (1 : Fin 8) 2 * swap (4 : Fin 8) 5 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (1 : Fin 8) 6 * swap (2 : Fin 8) 6 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (1 : Fin 8) 2 * swap (4 : Fin 8) 7 * swap (5 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (1 : Fin 8) 2 * swap (6 : Fin 8) 7),
   (swap (1 : Fin 8) 6 * swap (2 : Fin 8) 6 * swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7),
   (swap (1 : Fin 8) 6 * swap (2 : Fin 8) 6 * swap (4 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (4 : Fin 8) 7 * swap (6 : Fin 8) 7),
   (swap (4 : Fin 8) 5 * swap (6 : Fin 8) 7)]



theorem mem_tab_iff (L : List P8) (g : P8) : FF84.tab g ∈ L.map FF84.tab ↔ g ∈ L := by
  constructor
  · intro h
    obtain ⟨c, hc, hceq⟩ := List.mem_map.1 h
    rw [FF84.tab_inj hceq] at hc
    exact hc
  · intro h
    exact List.mem_map.2 ⟨g, h, rfl⟩

theorem tab_mul_eq_iff (g a : P8) :
    g * a = a * g ↔ FF84.comp (FF84.tab g) (FF84.tab a) = FF84.comp (FF84.tab a) (FF84.tab g) := by
  rw [← FF84.tab_mul, ← FF84.tab_mul]
  exact ⟨fun h => by rw [h], FF84.tab_inj⟩

theorem natCard_of_iff_finset' (H : Subgroup P8) (F : Finset P8) (h : ∀ x, x ∈ H ↔ x ∈ F) :
    Nat.card H = F.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_coe]

@[expose] def tabSub (L : List P8)
    (hmul : ∀ x ∈ L.map FF84.tab, ∀ y ∈ L.map FF84.tab, FF84.comp x y ∈ L.map FF84.tab)
    (hone : FF84.tab 1 ∈ L.map FF84.tab)
    (hinv : ∀ x ∈ L.map FF84.tab, ∃ y ∈ L.map FF84.tab, FF84.comp x y = FF84.tab 1) :
    Subgroup P8 where
  carrier := {g | FF84.tab g ∈ L.map FF84.tab}
  mul_mem' := by
    intro a b ha hb
    show FF84.tab (a * b) ∈ L.map FF84.tab
    rw [FF84.tab_mul]
    exact hmul _ ha _ hb
  one_mem' := by
    show FF84.tab 1 ∈ L.map FF84.tab
    exact hone
  inv_mem' := by
    intro a ha
    have ha' : FF84.tab a ∈ L.map FF84.tab := ha
    obtain ⟨y, hy, hyeq⟩ := hinv _ ha'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    have hac : a * c = 1 := by
      apply FF84.tab_inj
      rw [FF84.tab_mul]
      exact hyeq
    have hca : c = a⁻¹ := eq_inv_of_mul_eq_one_right hac
    show FF84.tab a⁻¹ ∈ L.map FF84.tab
    rw [← hca]
    exact List.mem_map.2 ⟨c, hc, rfl⟩

theorem natCard_tabSub (L : List P8)
    (hmul : ∀ x ∈ L.map FF84.tab, ∀ y ∈ L.map FF84.tab, FF84.comp x y ∈ L.map FF84.tab)
    (hone : FF84.tab 1 ∈ L.map FF84.tab)
    (hinv : ∀ x ∈ L.map FF84.tab, ∃ y ∈ L.map FF84.tab, FF84.comp x y = FF84.tab 1)
    (hnd : (L.map FF84.tab).Nodup) :
    Nat.card (tabSub L hmul hone hinv) = L.length := by
  have hnd' : L.Nodup := List.Nodup.of_map _ hnd
  have key : ∀ g : P8, g ∈ tabSub L hmul hone hinv ↔ g ∈ L.toFinset := by
    intro g
    rw [List.mem_toFinset]
    exact mem_tab_iff L g
  rw [natCard_of_iff_finset' _ L.toFinset key, List.toFinset_card_of_nodup hnd']

theorem Nat_card_A8s : Nat.card A8s = 20160 := by
  unfold A8s
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem sylow_contains {H R P : Subgroup P8} (hH : H ≤ A8s) (hR : R ≤ H)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hRp : IsPGroup 2 R)
    (hP : P ≤ H) (hPc : Nat.card P = 64) : R ≤ P := by
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 6) (by rw [hPc]; norm_num)
  have hPN : P ≤ Subgroup.normalizer (R : Set P8) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hRn p (hP hp) r hr
    · intro hr
      have h := hRn p⁻¹ (H.inv_mem (hP hp)) _ hr
      have e : p⁻¹ * (p * r * p⁻¹) * p⁻¹⁻¹ = r := by group
      rwa [e] at h
  have hK : IsPGroup 2 ↥(P ⊔ R) := IsPGroup.to_sup_of_normal_right' hPp hRp hPN
  have hKA : P ⊔ R ≤ A8s := sup_le (hP.trans hH) (hR.trans hH)
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hdvd : Nat.card ↥(P ⊔ R) ∣ 20160 := by
    have h := Subgroup.card_dvd_of_le hKA
    rwa [Nat_card_A8s] at h
  rw [hn] at hdvd
  have hcop : Nat.Coprime (2 ^ n) 315 := Nat.Coprime.pow_left n (by norm_num)
  have h2 : 2 ^ n ∣ 2 ^ 6 := by
    have e : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
    rw [e] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hle : 2 ^ n ≤ 2 ^ 6 := Nat.le_of_dvd (by norm_num) h2
  have hcardK : Nat.card ↥(P ⊔ R) ≤ 64 := by
    have e64 : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [e64] at hle
    rw [hn]
    exact hle
  have hPeq : P = P ⊔ R :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  have hRK : R ≤ P ⊔ R := le_sup_right
  rwa [← hPeq] at hRK


end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
