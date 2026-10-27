module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2CheckInputs
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.SmallOddCore.J2Data

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab
  CFSG.QuasithinUnique.Bridge.J2Excl

@[expose] def centPairCheck (n : ℕ) (gens : List PArr) (z x : Array ℕ) (wz wx : List ℤ)
    (prog : List (ℤ × ℤ)) (targets : List (Array ℕ)) : Bool :=
  let u := pWord n gens wz
  let v := pWord n gens wx
  eqA n (compA n u.1 z) (compA n z u.1) && eqA n (compA n v.1 x) (compA n x v.1) &&
    targets.all fun A => (pRun n [u, v] prog).any fun r => eqA n r.1 A

@[expose] def j2CentWZ1Str : String :=
  "-1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 2 1 -2 1 2 1 2 1 -2 1 2 1 -2"

@[expose] def j2CentWZ1 : List ℤ := parseInts j2CentWZ1Str

@[expose] def j2CentWX1Str : String :=
  "-2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -2 1 2 1 -2 1 2 1 -2 1 2 1 2 \
   1 -2 1 2 1 -2 1 -2 1 2 1 -2 -1 -2 -1 2 -1"

@[expose] def j2CentWX1 : List ℤ := parseInts j2CentWX1Str

@[expose] def j2CentProg1 : List (ℤ × ℤ) :=
  [(-2, 1), (3, -2), (4, 1), (5, 2), (6, 1), (7, 2), (8, 1), (9, 1), (10, 2), (11, -1), (12, -1),
   (13, -2), (14, 1), (15, -2), (16, -2), (17, -1), (18, -1), (19, -2), (20, -2), (21, 1), (22, 2),
   (23, 1), (24, 1), (25, 1), (26, 2), (27, 1), (28, 1), (29, 2), (1, -2), (31, -2), (32, 1),
   (33, -2), (34, -1), (35, -2), (36, -2), (37, -1), (38, -1), (39, 2), (40, -1), (41, 2), (42, 2)]

@[expose] def j2CentWZ2Str : String :=
  "-1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 \
   2 -1 2 -1 -2 -1 -2"

@[expose] def j2CentWZ2 : List ℤ := parseInts j2CentWZ2Str

@[expose] def j2CentWX2Str : String :=
  "1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 1 2 2 1 2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 -2 \
   1 2 1 2 1"

@[expose] def j2CentWX2 : List ℤ := parseInts j2CentWX2Str

@[expose] def j2CentProg2 : List (ℤ × ℤ) :=
  [(2, 1), (3, 2), (4, 1), (5, 2), (6, -1), (7, -2), (8, -1), (9, 2), (10, 1), (11, -2), (12, -1),
   (13, -2), (14, -2), (15, -2), (16, -1), (17, -2), (-1, -2), (19, -1), (20, -2), (21, -2),
   (22, 1), (23, 2), (24, 1), (25, -2)]

@[expose] def j2CentWZ7Str : String :=
  "2 1 -2 1 2 1 -2 1 -2 1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 2"

@[expose] def j2CentWZ7 : List ℤ := parseInts j2CentWZ7Str

@[expose] def j2CentWX7Str : String :=
  "-1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 \
   -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 -2"

@[expose] def j2CentWX7 : List ℤ := parseInts j2CentWX7Str

@[expose] def j2CentProg7 : List (ℤ × ℤ) :=
  [(1, 2), (3, -1), (4, -2), (5, -1), (6, -1), (7, 2), (8, 1), (9, 1), (10, 2), (11, 2), (12, -1),
   (13, -2), (2, -1), (15, -2), (16, -2), (17, -2), (18, -1), (19, 2), (20, 1), (21, -2), (22, -1),
   (23, 2), (24, 1), (25, -2), (26, 1), (27, 1), (28, 2), (29, 2), (30, 1), (31, 1), (32, 2),
   (33, -1), (34, -1), (35, -2), (36, 1), (37, 2), (38, 2), (39, 1)]

@[expose] def j2CentWZ54Str : String :=
  "2 1 -2 1 -2 1 2 1 -2 1 -2 1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 2"

@[expose] def j2CentWZ54 : List ℤ := parseInts j2CentWZ54Str

@[expose] def j2CentWX54Str : String :=
  "-1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 -2 -2 1 2 2 1 -2 1 2 1 -2 1 -2 1 2 \
   1 2 1 -2 1 -2 1 2 1 -2 1 -2 1"

@[expose] def j2CentWX54 : List ℤ := parseInts j2CentWX54Str

@[expose] def j2CentProg54 : List (ℤ × ℤ) :=
  [(1, 1), (3, 2), (4, 2), (5, 1), (6, 2), (7, 2), (8, 1), (9, 2), (10, 2), (11, 1), (12, 1),
   (1, 2), (14, 2), (15, 2), (16, 2), (17, 1), (18, -2), (19, -2), (20, -1), (21, 2), (22, -1),
   (23, 2), (24, 1), (25, -2), (26, 1)]

@[expose] def j2CentWZ58Str : String :=
  "-1 -2 -1 -2 -1 2 -1 -2 -1 -2 -2 -1 2 2 1 2 1 -2 1 -2 1 2 1 -2 1 2 1 -2 1 -2 1 2 1 2 1"

@[expose] def j2CentWZ58 : List ℤ := parseInts j2CentWZ58Str

@[expose] def j2CentWX58Str : String :=
  "2 1 2 1 -2 1 2 1 2 1 -2 1 2 1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 2"

@[expose] def j2CentWX58 : List ℤ := parseInts j2CentWX58Str

@[expose] def j2CentProg58 : List (ℤ × ℤ) :=
  [(2, 1), (3, 2), (4, -1), (5, 2), (6, 1), (7, 2), (8, 1), (9, 2), (10, 2), (11, 1), (12, -2),
   (13, 1), (14, -2), (15, -1), (16, 2), (17, 1), (18, -2), (19, -1), (20, -2), (21, 1), (22, -2),
   (23, -1), (24, 2), (25, -1), (26, -2), (27, -1), (28, -1), (29, 2), (30, 1), (31, 1), (2, 1),
   (33, 1), (34, -2), (35, -1), (36, -2), (37, -1), (38, -2), (39, 1), (40, 2), (41, 1), (42, -2),
   (43, 1), (44, 2), (45, -1), (46, -1), (47, 2), (48, -1), (49, -2), (50, -1), (51, -1), (52, 2),
   (53, -1)]

@[expose] def j2CentWZ165Str : String :=
  "2 -1 2 -1 -2 -1 -2 -1"

@[expose] def j2CentWZ165 : List ℤ := parseInts j2CentWZ165Str

@[expose] def j2CentWX165Str : String :=
  "-1 -2 -1 2 -1 -2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 \
   2 -1 -2 -1 2 -1 2 -1 -2 -1 2 -1 -2 -1 -2 -1 2 -1 -2 -1 2 -1 -2 -1 2 -1 2 -1 -2"

@[expose] def j2CentWX165 : List ℤ := parseInts j2CentWX165Str

@[expose] def j2CentProg165 : List (ℤ × ℤ) :=
  [(2, 1), (3, 1), (4, -2), (5, -1), (6, 2), (7, -1), (8, -1), (9, -1), (10, -1), (11, -1),
   (12, -2), (13, -1), (14, -1), (15, -2), (16, 1), (17, 2), (18, -1), (19, -1), (20, -1),
   (21, -1), (22, -2), (23, -1), (24, 2), (1, 2), (26, -1), (27, 2), (28, 1), (29, -2), (30, 1),
   (31, 1), (32, 2), (33, -1), (34, -1), (35, -2), (36, -2), (37, 1), (38, 2), (39, -1), (40, -1),
   (41, -1), (42, -1), (43, -2), (44, -1), (45, 2)]

@[expose] def j2CentData : List (ℕ × List ℤ × List ℤ × List (ℤ × ℤ)) :=
  [(1, j2CentWZ1, j2CentWX1, j2CentProg1),
   (2, j2CentWZ2, j2CentWX2, j2CentProg2),
   (7, j2CentWZ7, j2CentWX7, j2CentProg7),
   (54, j2CentWZ54, j2CentWX54, j2CentProg54),
   (58, j2CentWZ58, j2CentWX58, j2CentProg58),
   (165, j2CentWZ165, j2CentWX165, j2CentProg165)]

@[expose] def j2CentReps : List ℕ := j2CentData.map Prod.fst

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
