module

public import Certificates.Data.TabCo1Kit
public import Certificates.Data.TabCo1Reps
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public meta import Certificates.Data.TabCo1Kit
public meta import Certificates.Data.TabCo1Reps
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Five

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1Census

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Dickson.I271.TabCo1 Timmesfeld.Co1Five

@[expose] def ext : List (List Int) :=
  [
    [2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 87, 77, 60, 56, 82, 73, 58, 73, 58, 69, 87, 63, 66, 87, 73, 87, 77, 82, 77, 82],
    [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
    2, 2, 1, 2, 69, 87, 69, 56, 60, 69, 87, 58, 69, 63, 66, 66, 73, 77, 82, 82, 73, 77, 87],
    [1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
    1, 2, 77, 60, 55, 60, 82, 66, 87, 58, 77, 66, 87, 66, 63, 82, 87, 73, 77, 82, 82]]

@[expose] def steps : List (Nat × Nat × Nat) :=
  [
  (13, 1, 1), (48, 1, 2), (88, 5, 1), (90, 5, 2), (96, 6, 1), (113, 6, 2),
  (25, 13, 1), (119, 13, 2), (94, 48, 1), (21, 48, 2), (114, 88, 1), (115, 88, 2),
  (68, 90, 1), (121, 90, 2), (14, 96, 1), (84, 96, 2), (7, 113, 1), (117, 113, 2),
  (2, 25, 2), (78, 119, 1), (75, 119, 2), (55, 94, 1), (50, 21, 1), (83, 21, 2),
  (15, 114, 1), (10, 114, 2), (86, 115, 1), (123, 115, 2), (29, 68, 1), (58, 68, 2),
  (32, 121, 1), (81, 121, 2), (38, 14, 1), (12, 14, 2), (39, 84, 1), (73, 84, 2),
  (82, 117, 1), (66, 2, 2), (93, 78, 1), (85, 78, 2), (89, 75, 1), (4, 55, 1),
  (26, 83, 1), (109, 15, 1), (120, 15, 2), (46, 10, 1), (30, 10, 2), (118, 86, 1),
  (54, 86, 2), (28, 123, 1), (22, 123, 2), (35, 29, 1), (8, 58, 1), (102, 32, 1),
  (116, 38, 2), (42, 12, 1), (56, 39, 1), (112, 73, 1), (23, 73, 2), (43, 82, 1),
  (33, 66, 1), (17, 66, 2), (72, 93, 1), (105, 85, 1), (31, 85, 2), (122, 89, 1),
  (107, 4, 2), (45, 26, 2), (57, 109, 1), (70, 109, 2), (49, 120, 1), (63, 120, 2),
  (98, 46, 1), (80, 46, 2), (106, 30, 1), (92, 30, 2), (27, 28, 1), (101, 22, 2),
  (69, 35, 1), (103, 102, 1), (99, 116, 1), (16, 116, 2), (24, 112, 1), (71, 23, 1),
  (110, 33, 1), (100, 17, 1), (36, 17, 2), (104, 72, 1), (65, 105, 1), (40, 122, 1),
  (61, 107, 1), (9, 107, 2), (62, 45, 2), (20, 57, 1), (108, 70, 1), (64, 70, 2),
  (77, 49, 1), (44, 49, 2), (91, 63, 1), (47, 80, 1), (53, 106, 1), (111, 106, 2),
  (37, 92, 2), (76, 69, 2), (87, 103, 2), (18, 99, 1), (59, 24, 1), (3, 110, 1),
  (52, 36, 1), (124, 104, 1), (95, 61, 1), (67, 20, 1), (60, 20, 2), (74, 108, 1),
  (79, 64, 1), (11, 64, 2), (19, 44, 1), (51, 91, 1), (97, 76, 1), (41, 67, 1),
  (34, 60, 2)]

@[expose] def stepOK (D : List Rows × List Rows × Bool) (gR : List Rows) (cov : List Nat)
    (s : Nat × Nat × Nat) : Bool :=
  cov.contains s.2.1 && decide (s.1 < 125) && decide (s.2.2 < 3) &&
    mul (mul (nd D (88 + s.2.2)) (a0Row gR s.2.1)) (ndI D (88 + s.2.2)) == a0Row gR s.1

@[expose] def chainOK (D : List Rows × List Rows × Bool) (gR : List Rows) :
    List Nat → List (Nat × Nat × Nat) → Bool
  | _, [] => true
  | cov, s :: rest => stepOK D gR cov s && chainOK D gR (s.1 :: cov) rest

@[expose] def censusCheck (_ : Unit := ()) : Bool :=
  let D := kDag ext
  let gD := gDag aR bR
  let gR := gD.1
  D.2.2 && gD.2.2 && a0Row gR 1 == repD0 && a0Row gR 5 == repD1 && a0Row gR 6 == repZ &&
    chainOK D gR [1, 5, 6] steps &&
    (List.range 125).all fun k =>
      k == 0 || k == 1 || k == 5 || k == 6 || steps.any fun s => s.1 == k

end CFSG.HardMathSupport.Dickson.I271.TabCo1Census
