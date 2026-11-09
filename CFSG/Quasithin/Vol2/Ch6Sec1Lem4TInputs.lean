module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Quasithin.H13.Tits614

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def pWord : List ℤ := [1, -2, 3]

@[expose] def pArr : Array ℕ := wordArr 1755 titsHArrs pWord

@[expose] def pow5Arr (a : Array ℕ) : Array ℕ :=
  compA 1755 a (compA 1755 a (compA 1755 a (compA 1755 a a)))

@[expose] def eXWord (i : ℕ) : List ℤ := [[1], [1], [1], [1], [2]].getD i []

@[expose] def eYWord (i : ℕ) : List ℤ := [[1, 2], [1, 3], [1, 4], [2, 3], [1, 3]].getD i []

@[expose] def eXArr (i : ℕ) : Array ℕ := wordArr 1755 titsJArrs (eXWord i)

@[expose] def eYArr (i : ℕ) : Array ℕ := wordArr 1755 titsJArrs (eYWord i)

@[expose] def eGenArr (i : ℕ) : Array ℕ := commArr 1755 (eXArr i) (eYArr i)

@[expose] def eProdArr (v : ℕ) : Array ℕ :=
  (List.range 5).foldl (fun a i => if v.testBit i then compA 1755 a (eGenArr i) else a)
    (idA 1755)

@[expose] def eArrs : List (Array ℕ) := (List.range 32).map eProdArr

@[expose] def inE (a : Array ℕ) : Bool := anyEq eArrs a

@[expose] def inJ (a : Array ℕ) : Bool := siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 a

@[expose] def outerArr (a : Array ℕ) : Array ℕ := compA 1755 a titsGenArrs[1]!

@[expose] def ouRepWord (k : ℕ) : List ℕ :=
  [[], [0], [1], [2], [0,0], [0,1], [0,2], [1,0], [1,2], [2,0], [0,0,0], [0,0,1], [0,0,2],
    [0,1,0], [0,1,2], [0,2,0], [1,0,0], [1,0,1], [2,0,0], [2,0,1], [0,0,0,1], [0,0,0,2],
    [0,0,1,0], [0,0,1,2], [0,0,2,0], [0,1,0,0], [0,1,0,1], [0,2,0,0], [0,2,0,1], [1,0,0,0],
    [1,0,0,1], [1,0,0,2], [1,0,1,0], [2,0,0,0], [2,0,0,1], [0,0,0,1,0], [0,0,0,2,0],
    [0,0,1,0,0], [0,0,1,0,1], [0,0,2,0,0], [0,0,2,0,1], [0,1,0,0,0], [0,1,0,0,1], [0,1,0,0,2],
    [0,1,0,1,0], [0,2,0,0,1], [1,0,0,1,2], [1,0,0,2,0], [1,0,1,0,1], [0,0,0,1,0,0],
    [0,0,0,1,0,1], [0,0,0,2,0,0], [0,0,0,2,0,1], [0,0,1,0,0,0], [0,0,1,0,0,1], [0,0,1,0,0,2],
    [0,0,1,0,1,0], [0,0,2,0,0,1], [0,1,0,0,2,0], [0,0,0,1,0,0,1], [0,0,0,1,0,0,2],
    [0,0,0,1,0,1,0], [0,0,0,2,0,0,1], [0,0,1,0,0,2,0]].getD k []

@[expose] def ouRepArr (k : ℕ) : Array ℕ :=
  (ouRepWord k).foldl (fun a i => compA 1755 a titsSArrs[i]!) (idA 1755)

@[expose] def ouCov (g k : ℕ) : ℕ × ℕ :=
  [(1, 0), (4, 0), (5, 0), (6, 0), (10, 0), (11, 0), (12, 0), (13, 0), (14, 0), (15, 0),
    (0, 20), (20, 0), (21, 0), (22, 0), (23, 0), (24, 0), (25, 0), (26, 0), (27, 0), (28, 0),
    (2, 20), (3, 31), (35, 0), (33, 24), (36, 0), (37, 0), (38, 0), (39, 0), (40, 0), (41, 0),
    (42, 0), (43, 0), (44, 0), (8, 7), (45, 0), (7, 20), (9, 31), (49, 0), (50, 0), (51, 0),
    (52, 0), (53, 0), (54, 0), (55, 0), (56, 0), (57, 0), (47, 4), (58, 0), (29, 16),
    (16, 20), (17, 20), (18, 31), (19, 31), (48, 4), (59, 0), (60, 0), (61, 0), (62, 0),
    (63, 0), (30, 20), (31, 31), (32, 20), (34, 31), (46, 27), (2, 0), (7, 0), (0, 1), (8, 0),
    (16, 0), (17, 0), (9, 3), (1, 18), (3, 1), (6, 17), (29, 0), (30, 0), (31, 0), (32, 0),
    (19, 9), (18, 4), (4, 3), (5, 18), (15, 7), (14, 27), (44, 26), (45, 22), (42, 12),
    (46, 0), (47, 0), (38, 9), (48, 0), (33, 1), (34, 15), (10, 4), (11, 8), (12, 3), (13, 3),
    (27, 5), (28, 7), (50, 5), (52, 4), (54, 2), (25, 13), (57, 6), (43, 15), (56, 29),
    (22, 3), (40, 0), (20, 21), (21, 25), (23, 8), (24, 4), (26, 8), (61, 19), (35, 15),
    (60, 13), (36, 14), (59, 26), (37, 8), (58, 6), (41, 28), (39, 7), (55, 12), (53, 3),
    (51, 20), (49, 10), (63, 8), (62, 17), (3, 0), (9, 0), (8, 1), (0, 11), (18, 0), (19, 0),
    (7, 8), (6, 3), (2, 10), (1, 11), (33, 0), (34, 0), (32, 7), (31, 12), (17, 2), (16, 15),
    (15, 4), (14, 9), (4, 11), (5, 11), (21, 24), (20, 19), (40, 6), (48, 6), (38, 12),
    (47, 14), (46, 13), (29, 10), (30, 4), (27, 1), (28, 15), (13, 7), (12, 12), (10, 11),
    (11, 11), (36, 26), (35, 17), (55, 27), (24, 7), (56, 14), (22, 13), (57, 30), (43, 10),
    (42, 1), (45, 27), (44, 16), (26, 6), (25, 5), (23, 13), (51, 12), (52, 17), (49, 7),
    (50, 26), (63, 30), (58, 21), (37, 16), (39, 5), (41, 21), (54, 30), (62, 12), (61, 0),
    (60, 11), (59, 7), (53, 21)].getD (64 * g + k) (0, 0)

end CFSG.Quasithin.H13.Tits614
