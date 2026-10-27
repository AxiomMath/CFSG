module

public import CFSG.RankThree.Native.ONTripleSLP

public section

namespace CFSG.RankThree.Native.ONTriple

@[expose] def progM : List SOp := [
  .word [
    (3, false), (0, true), (2, true), (1, true), (3, false), (2, false), (1, false), (6, true),
    (3, false), (1, true), (6, false), (0, true), (2, true), (1, true), (3, false), (2, false),
    (1, false), (0, true), (2, true), (1, true), (3, false), (2, false), (1, false), (3, false),
    (1, false), (0, false), (6, true), (3, false), (1, true), (6, false), (0, true), (4, true),
    (6, false), (1, false), (6, false), (0, false), (3, false), (4, false), (1, false),
    (5, false), (3, false), (4, false), (4, false), (0, false), (0, false), (6, true),
    (1, false), (2, false), (3, false), (5, false), (5, false), (2, false), (6, false),
    (3, false), (1, false), (2, false), (1, false), (0, false), (6, true), (3, false),
    (1, true), (6, false), (0, true), (4, true), (6, false), (1, false), (6, false), (0, false),
    (3, false), (4, false), (1, false), (5, false), (3, false), (4, false), (4, false),
    (0, false), (0, false), (2, false), (1, false), (0, false), (3, false), (1, false),
    (2, false), (1, false), (0, false), (6, true), (3, false), (1, true), (6, false), (0, true),
    (4, true), (6, false), (1, false), (6, false), (0, false), (3, false), (4, false),
    (1, false), (5, false), (3, false), (4, false), (4, false), (0, false), (0, false),
    (6, true), (1, false), (2, false), (3, false), (5, false), (5, false), (2, false),
    (6, false), (3, false), (1, false), (2, false), (4, false), (2, false), (3, false),
    (2, false), (5, false), (6, false), (1, false), (2, false), (3, false), (4, false),
    (3, false), (2, false), (1, false), (5, false)],
  .word [
    (1, true), (6, true), (2, true), (3, true), (2, true), (3, true), (4, true), (1, true),
    (6, true), (2, true), (3, true), (0, true), (2, true), (4, true), (0, true), (0, true),
    (4, true), (4, true), (3, true), (5, true), (1, true), (4, true), (3, true), (0, true),
    (6, true), (1, true), (6, true), (4, false), (0, false), (6, true), (1, false), (3, true),
    (6, false), (0, true), (1, true), (2, true), (1, true), (3, true), (0, true), (1, true),
    (2, true), (0, true), (0, true), (4, true), (4, true), (3, true), (5, true), (1, true),
    (4, true), (3, true), (0, true), (6, true), (1, true), (6, true), (4, false), (0, false),
    (6, true), (1, false), (3, true), (6, false), (0, true), (1, true), (5, true), (0, true),
    (0, true), (4, true), (4, true), (3, true), (5, true), (1, true), (4, true), (3, true),
    (0, true), (6, true), (1, true), (6, true), (4, false), (0, false), (6, true), (1, false),
    (3, true), (6, false), (0, true), (1, true), (2, true), (1, true), (3, true), (6, true),
    (2, true), (5, true), (5, true), (3, true), (2, true), (1, true), (6, false), (0, true),
    (0, true), (4, true), (4, true), (3, true), (5, true), (1, true), (4, true), (3, true),
    (0, true), (6, true), (1, true), (6, true), (4, false), (0, false), (6, true), (1, false),
    (3, true), (6, false), (0, true), (1, true), (3, true), (0, true), (2, true), (1, true),
    (3, false), (2, false), (1, false), (6, true), (1, false), (3, true), (6, false), (1, true),
    (2, true), (3, true), (1, false), (2, false), (0, false), (1, false), (0, false), (3, true)],
  .word [
    (8, true), (9, true)],
  .word [
    (10, true), (9, true)],
  .word [
    (10, true), (11, true)],
  .word [
    (10, true), (12, true)],
  .word [
    (13, true), (10, true)],
  .word [
    (14, true), (11, true)],
  .word [
    (14, true), (15, true)],
  .word [
    (16, true), (16, true)],
  .word [
    (16, true), (16, true)],
  .word [
    (13, true), (11, true)],
  .pow 19 19,
  .pow 30 20,
  .word [
    (21, true), (18, true)],
  .word [
    (22, true), (20, true)],
  .word [
    (11, true), (13, true)],
  .word [
    (12, true), (11, true)],
  .word [
    (25, true), (10, true)],
  .pow 12 26,
  .word [
    (24, true), (27, true)],
  .pow 14 28,
  .word [
    (29, true), (17, true)],
  .word [
    (30, true), (28, true)],
  .word [
    (23, true), (31, true)],
  .word [
    (32, true), (31, true)],
  .pow 4 33,
  .word [
    (23, true), (23, true)],
  .word [
    (35, true), (31, true)],
  .word [
    (36, true), (31, true)],
  .pow 2 37,
  .word [
    (23, true), (31, true)],
  .word [
    (39, true), (31, true)],
  .word [
    (40, true), (23, true)],
  .pow 2 41,
  .word [
    (31, true), (23, true)],
  .word [
    (43, true), (31, true)],
  .pow 4 44,
  .word [
    (2, true), (0, true)],
  .word [
    (3, true), (5, false)],
  .word [
    (1, true), (47, true)],
  .word [
    (5, true), (47, true)],
  .word [
    (49, true), (0, true)],
  .word [
    (47, true), (7, false)],
  .word [
    (1, true), (46, false)],
  .word [
    (0, true), (6, true)],
  .word [
    (48, true), (50, true)],
  .word [
    (50, true), (7, true)],
  .word [
    (52, true), (7, false)],
  .word [
    (0, true), (54, false)],
  .word [
    (56, true), (7, false)],
  .word [
    (55, true), (54, true)],
  .word [
    (51, true), (46, false)],
  .word [
    (58, true), (46, true)],
  .word [
    (59, true), (54, false)],
  .word [
    (60, true), (7, true)],
  .word [
    (62, true), (7, true)],
  .word [
    (63, true), (6, true)],
  .word [
    (4, true), (46, false)],
  .word [
    (53, true), (54, false)],
  .word [
    (6, true), (7, false)],
  .word [
    (46, true), (54, false)],
  .word [
    (7, true), (57, true)],
  .word [
    (64, true), (61, true)],
  .word [
    (67, true), (68, true)],
  .word [
    (69, true), (71, true)],
  .word [
    (70, true), (61, true)],
  .word [
    (54, true), (68, true)],
  .word [
    (66, true), (57, true)],
  .word [
    (73, true), (76, true)],
  .word [
    (68, true), (75, true)],
  .word [
    (57, true), (61, false)],
  .word [
    (74, true), (72, false)],
  .word [
    (76, true), (75, true)],
  .word [
    (71, true), (61, false)],
  .word [
    (77, true), (72, true)],
  .word [
    (81, true), (65, true)],
  .word [
    (72, true), (78, true)],
  .word [
    (85, true), (65, false)],
  .word [
    (86, true), (83, true)],
  .word [
    (65, true), (75, true)],
  .word [
    (82, true), (79, false)],
  .word [
    (84, true), (88, false)],
  .word [
    (87, true), (75, true)],
  .word [
    (79, true), (91, false)],
  .word [
    (88, true), (89, true)],
  .word [
    (92, true), (90, true)],
  .word [
    (93, true), (90, false)],
  .word [
    (75, true), (83, true)],
  .word [
    (78, true), (80, false)],
  .word [
    (97, true), (96, true)],
  .word [
    (89, true), (98, true)],
  .word [
    (90, true), (80, true)],
  .word [
    (80, true), (99, true)],
  .word [
    (100, true), (96, true)],
  .word [
    (61, true), (99, false)],
  .word [
    (95, true), (99, true)],
  .word [
    (103, true), (104, false)],
  .word [
    (105, true), (96, false)],
  .word [
    (106, true), (102, false)],
  .word [
    (104, true), (102, true)],
  .word [
    (99, true), (107, true)],
  .word [
    (107, true), (98, false)],
  .word [
    (98, true), (109, false)],
  .word [
    (102, true), (110, true)],
  .word [
    (91, true), (112, false)],
  .word [
    (110, true), (96, false)],
  .word [
    (83, true), (114, true)],
  .word [
    (115, true), (96, false)],
  .word [
    (111, true), (94, false)],
  .word [
    (116, true), (101, true)],
  .word [
    (113, true), (108, true)],
  .word [
    (108, true), (101, false)],
  .word [
    (119, true), (109, false)],
  .word [
    (117, true), (112, true)],
  .word [
    (114, true), (94, false)],
  .word [
    (122, true), (112, true)],
  .word [
    (96, true), (118, false)],
  .word [
    (124, true), (109, false)],
  .word [
    (112, true), (126, false)],
  .word [
    (101, true), (125, false)],
  .word [
    (121, true), (109, true)],
  .word [
    (128, true), (129, true)],
  .word [
    (118, true), (109, true)],
  .word [
    (123, true), (109, true)],
  .word [
    (132, true), (127, false)],
  .word [
    (120, true), (125, true)],
  .word [
    (130, true), (134, false)],
  .word [
    (94, true), (125, true)],
  .word [
    (133, true), (126, false)],
  .word [
    (131, true), (136, false)],
  .word [
    (138, true), (126, false)],
  .word [
    (137, true), (136, false)],
  .word [
    (140, true), (109, false)],
  .word [
    (129, true), (127, true)],
  .word [
    (141, true), (135, true)],
  .word [
    (134, true), (135, false)],
  .word [
    (125, true), (136, false)],
  .word [
    (136, true), (109, false)],
  .word [
    (143, true), (142, false)],
  .word [
    (145, true), (109, false)],
  .word [
    (148, true), (109, false)],
  .word [
    (127, true), (147, true)],
  .word [
    (147, true), (126, false)],
  .word [
    (151, true), (144, false)],
  .word [
    (146, true), (149, true)],
  .word [
    (153, true), (149, false)],
  .word [
    (149, true), (135, false)],
  .word [
    (152, true), (154, false)],
  .word [
    (144, true), (139, false)],
  .word [
    (142, true), (139, false)],
  .word [
    (155, true), (156, true)],
  .word [
    (150, true), (159, true)],
  .word [
    (135, true), (109, false)],
  .word [
    (109, true), (160, true)],
  .word [
    (154, true), (159, true)],
  .word [
    (161, true), (162, false)],
  .word [
    (158, true), (160, true)],
  .word [
    (160, false), (157, false), (157, false), (139, false), (159, false), (163, true),
    (160, true), (126, false), (126, true), (160, true), (162, false), (165, true),
    (139, false), (165, false), (160, false), (139, false)],
  .word [
    (157, false), (159, false), (164, true), (163, true), (164, true), (165, false),
    (156, true), (126, true), (157, true), (164, false), (126, false), (157, false),
    (159, true), (162, true), (126, false), (157, true)],
  .word [
    (159, false), (164, true), (165, true), (163, false), (165, false), (163, false),
    (165, true), (163, false), (159, false), (156, true), (157, false), (165, true),
    (157, false), (157, false), (162, true), (164, false)],
  .word [
    (166, false), (167, false), (166, true), (167, true)],
  .word [
    (166, false), (168, false), (166, true), (168, true)],
  .word [
    (169, true), (170, true), (169, true), (170, true), (169, false), (170, true), (169, true),
    (170, false)],
  .word [
    (170, true), (169, true), (170, true), (169, true), (170, false), (169, true), (170, true),
    (169, false), (170, false)],
  .word [
    (169, true), (170, true), (169, false), (170, false), (169, false), (170, false),
    (169, true), (170, true), (169, false), (170, false)],
  .word [
    (169, true), (170, false), (169, false), (170, true), (169, true), (170, false),
    (169, true), (170, true)],
  .word [
    (169, false), (170, true), (169, true), (170, false), (169, true), (170, true), (169, true),
    (170, true)],
  .word [
    (169, true), (170, true), (169, true), (170, false), (169, true), (170, true), (169, true),
    (170, true), (169, true)],
  .word [
    (170, true), (169, false), (170, false), (169, true), (170, true), (169, false),
    (170, false), (169, true), (170, true)],
  .word [
    (169, false), (170, true), (169, false), (170, true)],
  .word [
    (169, true), (170, true), (169, true), (170, false), (169, false), (170, true), (169, true),
    (170, true), (169, true)],
  .word [
    (169, true), (170, false), (169, true), (170, true), (169, true), (170, true), (169, false),
    (170, true)],
  .word [
    (170, true), (169, true), (170, true), (169, false), (170, true), (169, true), (170, false)],
  .word [
    (169, true), (170, true), (169, true), (170, true), (169, true), (170, true), (169, false),
    (170, true), (169, true), (170, true), (169, false)],
  .word [
    (169, false), (170, false), (169, true), (170, true), (169, false), (170, false),
    (169, true), (170, true), (169, false), (170, false)],
  .word [
    (170, true), (169, true), (170, false), (169, true), (170, true)],
  .word [
    (169, false), (170, false), (169, true), (170, true), (169, false), (170, false),
    (169, false), (170, true)],
  .word [
    (170, true), (169, true), (170, true), (169, true), (170, false), (169, false), (170, true),
    (169, true), (170, true)],
  .word [
    (169, true), (170, false), (169, true), (170, false)],
  .word [
    (169, true), (170, true), (169, false), (170, false), (169, true), (170, true),
    (169, false), (170, false), (169, true)],
  .word [
    (31, true), (23, true), (23, true), (23, true), (31, true), (23, true), (23, true),
    (31, true), (23, true), (31, true)],
  .word [
],
  .word [
    (23, true), (31, true), (23, true), (23, true), (23, true), (31, true), (23, true),
    (31, true), (23, true), (23, true), (23, true)],
  .word [
    (23, true), (31, true), (23, true), (23, true), (23, true), (31, true), (23, true),
    (31, true), (23, true)],
  .word [
    (31, true), (23, true), (23, true), (31, true)],
  .word [
],
  .word [
    (23, true), (31, true), (23, true), (31, true), (23, true), (23, true), (23, true),
    (31, true), (23, true), (31, true), (23, true)],
  .word [
    (23, true), (31, true), (23, true), (23, true), (23, true), (31, true), (23, true),
    (31, true), (23, true), (23, true), (23, true), (31, true), (23, true)],
  .word [
    (38, true), (42, true)],
  .word [
    (170, true), (169, true), (170, true), (169, true), (170, false), (169, false),
    (170, false), (169, true)],
  .word [
    (169, true), (170, true), (169, false), (170, false), (169, false), (170, false),
    (169, true), (170, true), (169, true), (170, false), (169, false)]]

@[expose] def rX : List ℕ := [34, 38, 42, 45]

abbrev rN1 : ℕ := 23

abbrev rN2 : ℕ := 31

abbrev rK1 : ℕ := 169

abbrev rK2 : ℕ := 170

abbrev rX12 : ℕ := 197

abbrev rY1 : ℕ := 198

abbrev rY3 : ℕ := 199

@[expose] def rV : List (List (List ℕ)) :=
  [[[171, 172, 173], [174, 175, 176], [177, 178, 179]],
    [[180, 181, 182], [183, 184, 185], [186, 187, 188]]]

@[expose] def rL : List (List ℕ) := [[189, 190, 191, 192], [193, 194, 195, 196]]

@[expose] def witData : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(0, 0, 1, 0, 0), (0, 0, 1, 0, 1), (0, 0, 1, 0, 2), (0, 0, 1, 1, 0), (0, 0, 1, 1, 1),
    (0, 0, 1, 1, 2), (0, 0, 1, 2, 0), (0, 0, 1, 2, 1), (0, 0, 1, 2, 2), (0, 0, 2, 0, 0),
    (0, 0, 2, 0, 1), (0, 0, 2, 0, 2), (0, 0, 2, 1, 0), (0, 0, 2, 1, 1), (0, 0, 2, 1, 2),
    (0, 0, 2, 2, 0), (0, 0, 2, 2, 1), (0, 0, 2, 2, 2), (0, 0, 3, 0, 0), (0, 0, 3, 0, 1),
    (0, 0, 3, 0, 2), (0, 0, 3, 1, 0), (0, 0, 3, 1, 1), (0, 0, 3, 1, 2), (0, 0, 3, 2, 0),
    (0, 0, 3, 2, 1), (0, 0, 3, 2, 2), (0, 1, 2, 0, 0), (0, 1, 2, 0, 1), (0, 1, 2, 0, 2),
    (0, 1, 2, 1, 0), (0, 1, 2, 1, 1), (0, 1, 2, 1, 2), (0, 1, 2, 2, 0), (0, 1, 2, 2, 1),
    (0, 1, 2, 2, 2), (0, 1, 3, 0, 0), (0, 1, 3, 0, 1), (0, 1, 3, 0, 2), (0, 1, 3, 1, 0),
    (0, 1, 3, 1, 1), (0, 1, 3, 1, 2), (0, 1, 3, 2, 0), (0, 1, 3, 2, 1), (0, 1, 3, 2, 2),
    (0, 2, 3, 0, 0), (0, 2, 3, 0, 1), (0, 2, 3, 0, 2), (0, 2, 3, 1, 0), (0, 2, 3, 1, 1),
    (0, 2, 3, 1, 2), (0, 2, 3, 2, 0), (0, 2, 3, 2, 1), (0, 2, 3, 2, 2), (1, 0, 1, 0, 0),
    (1, 0, 1, 0, 1), (1, 0, 1, 0, 2), (1, 0, 1, 1, 0), (1, 0, 1, 1, 1), (1, 0, 1, 1, 2),
    (1, 0, 1, 2, 0), (1, 0, 1, 2, 1), (1, 0, 1, 2, 2), (1, 0, 2, 0, 0), (1, 0, 2, 0, 1),
    (1, 0, 2, 0, 2), (1, 0, 2, 1, 0), (1, 0, 2, 1, 1), (1, 0, 2, 1, 2), (1, 0, 2, 2, 0),
    (1, 0, 2, 2, 1), (1, 0, 2, 2, 2), (1, 0, 3, 0, 0), (1, 0, 3, 0, 1), (1, 0, 3, 0, 2),
    (1, 0, 3, 1, 0), (1, 0, 3, 1, 1), (1, 0, 3, 1, 2), (1, 0, 3, 2, 0), (1, 0, 3, 2, 1),
    (1, 0, 3, 2, 2), (1, 1, 2, 0, 0), (1, 1, 2, 0, 1), (1, 1, 2, 0, 2), (1, 1, 2, 1, 0),
    (1, 1, 2, 1, 1), (1, 1, 2, 1, 2), (1, 1, 2, 2, 0), (1, 1, 2, 2, 1), (1, 1, 2, 2, 2),
    (1, 1, 3, 0, 0), (1, 1, 3, 0, 1), (1, 1, 3, 0, 2), (1, 1, 3, 1, 0), (1, 1, 3, 1, 1),
    (1, 1, 3, 1, 2), (1, 1, 3, 2, 0), (1, 1, 3, 2, 1), (1, 1, 3, 2, 2), (1, 2, 3, 0, 0),
    (1, 2, 3, 0, 1), (1, 2, 3, 0, 2), (1, 2, 3, 1, 0), (1, 2, 3, 1, 1), (1, 2, 3, 1, 2),
    (1, 2, 3, 2, 0), (1, 2, 3, 2, 1), (1, 2, 3, 2, 2)]

end CFSG.RankThree.Native.ONTriple
