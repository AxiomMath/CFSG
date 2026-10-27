module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Sporadic.HeldB.CertPChainData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import CFSG.Certificates.CosetTableShort
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def hjGens : List PArr :=
  [(heGen 0, invCand 8330 (heGen 0)), (heGen 1, invCand 8330 (heGen 1))]

@[expose] def hjProg : List (ℤ × ℤ) :=
    [(1, 0), (1, 2), (4, -2), (5, -2), (6, -2), (7, 1), (8, 2), (9, 2), (10, 2), (11, -2),
     (12, 1), (13, 2), (14, -2), (15, -2), (16, -2), (17, 1), (18, 2), (19, 2), (20, 2), (21, -2),
     (22, 1), (23, 2), (24, -2), (25, -2), (26, -2), (27, 1), (28, 2), (29, 2), (30, 2), (31, -2),
     (2, -2), (33, 1), (34, 2), (35, -2), (36, 2), (37, -2), (38, -1), (39, 2), (40, -2),
     (41, -1), (42, 2), (43, -2), (44, 1), (45, 2), (46, -2), (47, -1), (-2, 2), (49, 1), (50, 1),
     (51, -2), (52, 1), (53, 2), (54, -2), (55, -1), (56, 2), (57, -1), (58, -1), (59, -2),
     (60, 2), (61, -1), (62, -2), (63, 2), (64, 1), (65, 1), (66, -2), (67, 1), (68, 2), (69, -1),
     (70, -2), (71, -1), (72, 2), (73, -1), (74, -1), (75, -2), (76, 2), (77, -1), (78, -2),
     (79, 2), (80, 1), (81, 1), (82, -2), (83, 1), (84, 2), (85, -1), (1, -1), (87, 2), (88, 1),
     (89, -2), (90, 1), (91, 1), (92, -1), (93, 2), (94, 1), (95, -2), (96, 1), (97, 1), (98, -1),
     (99, 2), (100, 1), (101, -2), (102, 1), (1, 2), (104, 2), (105, -1), (106, -2), (107, 2),
     (108, -2), (109, 1), (110, 2), (111, -2), (112, 2), (113, 1), (114, -2), (115, -2), (116, 1),
     (117, 2), (118, 2), (119, -1), (120, -2), (121, 2), (122, -2), (123, 1), (124, 2), (125, -2),
     (126, 2), (127, 1), (128, -2), (129, -2), (130, 1), (131, 2), (132, 2), (133, -1), (134, -2),
     (135, 2), (136, -2), (137, 1), (138, 2), (139, -2), (140, 2), (141, 1), (142, -2), (143, -2),
     (1, -2), (145, -1), (146, 2), (147, -2), (148, 1), (149, 2), (150, -2), (151, 1), (152, 2),
     (153, 1), (154, -2), (155, -1), (156, 2), (157, -2), (158, 1), (159, 2), (160, -2), (161, 1),
     (162, 2), (163, 1), (164, -2), (165, -1), (166, 2), (167, -2), (168, 1), (169, 2), (170, -2),
     (171, 1), (172, 2), (1, -2), (174, 1), (175, 2), (176, 1), (177, -2), (178, 1), (179, 2),
     (180, 1), (181, -2), (182, 1), (183, 2), (1, -1), (185, 2), (186, 2), (187, 1), (188, -2),
     (189, -2), (190, 1), (191, 1), (192, -1), (193, 2), (194, 2), (195, 1), (196, -2), (197, -2),
     (198, 1), (199, 1), (200, -1), (201, 2), (202, 2), (203, 1), (204, -2), (205, -2), (206, 1),
     (-32, -173), (208, 103), (209, -86), (210, 173), (211, -173), (212, 86), (213, 48),
     (214, -86), (215, 207), (216, 216), (-32, -48), (218, -48), (219, 173), (220, -32),
     (221, -144), (222, -184), (223, 32), (224, -103), (225, 32), (226, 226), (227, 217),
     (228, 227), (229, 217), (230, -227), (231, 217), (232, -227), (233, 217), (234, -227),
     (235, -217), (236, -227), (237, -217), (238, 227), (239, -217), (240, 227), (241, -217),
     (242, -227), (243, -227), (244, -227), (245, 217), (246, 227), (247, -217), (248, 227),
     (249, 227), (-227, -227), (251, 217), (252, 227), (253, 217), (254, 227), (255, 217),
     (256, 227), (257, 227), (258, 217), (259, 227), (260, 217), (261, 227), (262, 217),
     (263, 227), (264, 227), (265, -217), (266, -227), (267, -217), (268, -227), (269, -217),
     (270, -227), (271, -227), (272, -217), (273, -227), (274, -217), (275, -227), (276, -217),
     (2, 2), (278, 2), (279, 2), (280, 2), (281, 2), (282, 1), (283, 282), (284, 1), (285, 282),
     (286, 1), (287, 279), (288, 1), (289, 279), (290, 1), (291, 2), (292, 1), (293, 280),
     (294, 1), (295, 278), (296, 1), (297, 279), (298, 1), (299, 280), (300, 1), (301, 281),
     (302, 1), (303, 281), (304, 1), (305, 278), (306, 1), (307, 280), (308, 1), (309, 281),
     (310, 1), (311, 2), (312, 1), (279, 1), (314, 282), (315, 1), (316, 282), (317, 1),
     (318, 278), (319, 1), (320, 280), (321, 1), (322, 280), (323, 1), (324, 281), (325, 1),
     (326, 2), (327, 1), (328, 280), (329, 1), (330, 279), (331, 1), (332, 279), (333, 1),
     (334, 279), (335, 1), (336, 278), (337, 1), (338, 281), (339, 1), (340, 279), (341, 1),
     (342, 2), (343, 1), (278, 1), (345, 278), (346, 1), (347, 279), (348, 1), (349, 280),
     (350, 1), (351, 278), (352, 1), (353, 279), (354, 1), (355, 2), (356, 1), (357, 279),
     (358, 1), (359, 278), (360, 1), (361, 278), (362, 1), (363, 2), (364, 1), (365, 280),
     (366, 1), (367, 2), (368, 1), (369, 282), (370, 1), (371, 281), (372, 1), (373, 282),
     (374, 1)]

@[expose] def hjRegs : List PArr := pRun 8330 hjGens hjProg

@[expose] def hjLetA : ℤ := 250

@[expose] def hjLetB : ℤ := 277

@[expose] def hjLetG : ℤ := 32

@[expose] def hjLabels : List (ℕ × ℕ × ℕ × ℤ) :=
  [(4, 1, 0, 313), (8, 1, 1, 344), (12, 1, 1, 375)]

@[expose] def hjA : PArr := pLetter 8330 hjRegs hjLetA

@[expose] def hjB : PArr := pLetter 8330 hjRegs hjLetB

@[expose] def hjG : PArr := pLetter 8330 hjRegs hjLetG

@[expose] def hjLet (x y : PArr) (l : Fin 2 × Bool) : PArr :=
  if l.1.val = 0 then (if l.2 then x else pInv x) else (if l.2 then y else pInv y)

@[expose] def hjWord (x y : PArr) : List (Fin 2 × Bool) → PArr
  | [] => pId 8330
  | l :: w => pMul 8330 (hjLet x y l) (hjWord x y w)

@[expose] def hjZ1 : PArr := hjWord hjA hjB zOne

@[expose] def hjNF (k a b : ℕ) : Array ℕ :=
  compA 8330 (compA 8330 (hjWord hjA hjB (tw k)).1 (if a = 1 then hjZ1.1 else idA 8330))
    (if b = 1 then heGen 0 else idA 8330)

@[expose] def hjComm (x y : Array ℕ) : Bool := eqA 8330 (compA 8330 x y) (compA 8330 y x)

@[expose] def hjLabelOK (l : ℕ × ℕ × ℕ × ℤ) : Bool :=
  eqA 8330 (compA 8330 (compA 8330 (pLetter 8330 hjRegs l.2.2.2).1 (heGen 0))
    (pLetter 8330 hjRegs l.2.2.2).2) (compA 8330 (heGen 0) (hjNF l.1 l.2.1 l.2.2.1))

@[noinline, expose] def hjFusOK : Bool :=
  hjComm hjA.1 (heGen 0) && hjComm hjB.1 (heGen 0) &&
    (coverWs ++ [zThree]).all (fun w => eqA 8330 (hjWord hjA hjB w).1 (idA 8330)) &&
    eqA 8330 (hjWord hjA hjB zTwo).1 (heGen 0) &&
    eqA 8330 (compA 8330 hjZ1.1 hjZ1.1) (idA 8330) && !(eqA 8330 hjZ1.1 (idA 8330)) &&
    !(eqA 8330 hjZ1.1 (heGen 0)) && !(hjComm hjA.1 hjB.1) && hjComm hjG.1 (heGen 0) &&
    !(hjComm hjG.1 hjZ1.1) && hjLabels.all hjLabelOK

end CFSG.ComponentClassification.GSThmB.CF23L34
