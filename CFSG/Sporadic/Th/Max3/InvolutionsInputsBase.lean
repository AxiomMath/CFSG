
module

public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.InvRep

open CFSG.Sporadic.Th.Native

@[expose] def wordOfString (s : String) : List Gen :=
  s.toList.map fun c => if c = 'x' then Gen.x else Gen.y

@[expose] def conjTable : List (Nat × String) :=
  [(2, ""), (3, "yxyxyxyxyxyx"), (4, "x"), (5, "xyxyxyxyxyxyx"), (8, "yyyyx"), (9, "xyxyxyxyxyx"),
   (12, "yyyyxyx"), (13, "xyyyyxyxyxyyyxyx"), (14, "yyyxyyyyxyxyx"), (15, "yyxyyxyyxyyyx"),
   (16, "yxyxyxyxyx"), (17, "xyyyyx"), (18, "yyyyxyxyxyyyxyx"), (19, "xyyyyxyx"),
   (22, "xyyyxyyyyxyxyx"), (23, "xyyxyyxyyxyyyx"), (24, "yyyyxyyyxyyyxyx"), (25, "yxyyxyyyx"),
   (32, "yyyx"), (33, "xyxyyyxyxyyyyx"), (34, "yyyxyx"), (35, "yyxyyyxyyxyyyyx"),
   (36, "yyxyyxyyxyx"), (37, "xyxyxyxyyxyxyyyx"), (42, "yxyyxyyxyyyx"), (43, "yyxyyyyxyxyx"),
   (52, "xyyyyyxyxyyyx"), (53, "yxyxyyxyyxyyyx"), (56, "yyyyxyyyyxyyyx"), (57, "yxyyxyxyyyx"),
   (64, "yyyyyxyyyyx"), (65, "xyxyxyxyx"), (68, "xyyyxyxyyxyx"), (69, "yxyyxyyyyxyyyx"),
   (70, "xyxyxyyyyx"), (71, "yxyyxyxyyyyx"), (72, "xyyyyxyyxyx"), (73, "yyyxyxyxyyyxyx"),
   (74, "xyyyxyyxyyyxyx"), (75, "yyyxyyyyyxyxyyyx"), (76, "yyyyyxyyxyx"), (77, "xyyxyxyxyyyxyx"),
   (82, "xyxyx"), (83, "yyyxyyxyyyyx"), (84, "xyyyxyxyyyyx"), (85, "yyyyyxyyyx"),
   (86, "yyxyyyxyyxyyyx"), (87, "yyyyyxyyyxyx"), (92, "xyxyxyyxyxyyyx"), (93, "yyxyyxyyyxyyyx"),
   (96, "xyyxyyyx"), (97, "yyyxyyyxyyyxyx"), (100, "yyxyyyxyyyx"), (101, "yyyxyyyyxyxyyxyx"),
   (102, "xyyyxyxyyyx"), (103, "yxyyyyxyxyyyyx"), (110, "yxyyyxyxyx"), (111, "yyyxyyyyx"),
   (112, "yxyyxyyyyxyx"), (113, "xyxyyyxyx"), (124, "xyxyyxyyyxyxyx"), (125, "yyyyxyxyyyx"),
   (128, "xyyyx"), (129, "yxyyyxyxyyyyx"), (130, "xyyxyyxyyxyx"), (131, "yxyxyxyyxyxyyyx"),
   (132, "xyyyxyx"), (133, "yyyxyyyxyyxyyyx"), (138, "yxyxyyxyyyxyxyx"), (139, "yyyyyxyxyyyx"),
   (148, "xyyxyyyyxyxyx"), (149, "xyxyyxyyxyyyx"), (152, "yxyyyyyxyxyyyx"), (153, "xyxyyxyxyyyx"),
   (160, "yxyyxyyxyyxyx"), (161, "yyxyxyxyyxyxyyyx"), (162, "xyxyyyx"), (163, "xyyxyyyxyxyyyyx"),
   (164, "yxyyyx"), (165, "yyxyyyxyxyyyyx"), (168, "yxyxyyyx"), (169, "xyyxyxyyyyyxyxyx"),
   (172, "xyyxyyxyyyxyx"), (173, "yyyxyxyxyyxyxyyyx"), (174, "yyxyxyyyx"), (175, "xyyyxyyyyxyyyx"),
   (176, "yyxyxyyyyyxyxyx"), (177, "yyyxyyxyx"), (178, "yyyyxyxyxyyyxyxyx"), (179, "yyxyyxyyyxyx"),
   (182, "xyyxyxyyyx"), (183, "yyyxyyyyxyyyx"), (184, "yxyxyxyyyxyx"), (185, "yyyxyyyyxyx"),
   (194, "yxyxyyyyyxyxyx"), (195, "yyxyyxyx"), (200, "xyxyyyxyxyyyx"), (201, "yyxyyyyxyyyx"),
   (202, "yxyyxyyyxyx"), (203, "yyyxyxyxyyyxyxyx"), (204, "xyyyyxyyyyx"), (205, "xyyxyyyxyxyx"),
   (210, "xyx"), (211, "xyxyxyxyxyxyxyx"), (212, "xyyyxyyxyyxyyyx"), (213, "yxyyxyyxyx"),
   (214, "yyxyxyxyxyxyxyx"), (215, "yyx"), (216, "yyxyxyyyyx"), (217, "xyxyxyxyyyyx"),
   (218, "yxyyxyyyxyyxyyyx"), (219, "xyxyyyxyxyyxyx"), (222, "yyxyx"), (223, "yxyyyxyyxyyyyx"),
   (226, "xyxyxyyyxyx"), (227, "yyxyyyyxyx"), (238, "yyxyyxyyyxyxyx"), (239, "xyyxyyxyxyyyx"),
   (240, "xyyyyxyyxyyyyx"), (241, "xyxyxyx"), (248, "yyxyxyyxyx"), (249, "yyyxyyyyyxyxyx"),
   (250, "xyxyyyyx"), (251, "xyyxyxyxyxyx"), (254, "yxyyyyxyxyx"), (255, "xyyxyyxyyyx"),
   (256, "yxyxyxyx"), (257, "xyyyyyxyyyyx"), (258, "yyyyxyyyyyxyxyx"), (259, "yyyxyxyyxyx"),
   (262, "yxyxyyyyx"), (263, "yxyyxyxyxyxyx"), (266, "yyyxyxyyyyx"), (267, "xyyyyyxyyyx"),
   (268, "yxyx"), (269, "xyyyxyyxyyyyx"), (270, "xyyyyyxyyyxyx"), (271, "xyyxyyyxyyxyyyx"),
   (272, "yyyyxyyxyx"), (273, "xyyyxyxyxyyyxyx"), (274, "xyyyyyxyyxyx"), (275, "yyxyxyxyyyxyx"),
   (276, "yyyxyyxyyyxyx"), (277, "xyyyxyyyyyxyxyyyx"), (282, "yyxyyyyyxyxyyyx"),
   (283, "yxyxyyxyxyyyx"), (292, "xyxyxyyyyyxyxyx"), (293, "xyyxyyxyx"), (298, "xyxyyxyyxyx"),
   (299, "yyyxyyxyyxyyyx"), (300, "yxyxyxyxyxyxyx"), (301, "yx"), (302, "xyyxyxyxyxyxyxyx"),
   (303, "xyyx"), (304, "xyyxyyyyxyyyx"), (305, "yxyyyxyxyyyx"), (306, "yyxyyyxyxyx"),
   (307, "yyyyxyyyyx"), (308, "xyyyxyxyxyyyxyxyx"), (309, "xyxyyxyyyxyx"), (312, "xyyxyxyyyyx"),
   (313, "yxyxyxyyyyx"), (316, "yyxyyxyyyyxyyyx"), (317, "yxyyyxyxyyxyx"),
   (318, "yxyyxyxyxyyyxyx"), (319, "xyyxyx"), (322, "yxyyyxyyyxyx"), (323, "yyyyxyyxyyyx"),
   (324, "yyxyyyxyyyyx"), (325, "yyxyxyyyxyxyx"), (326, "yyyyxyyxyxyyyx"), (327, "yxyyyyxyyyx"),
   (328, "xyxyyxyyyxyyyx"), (329, "yxyyxyyyxyyyxyx"), (330, "xyyyxyyyx"), (331, "yxyyyyxyxyyxyx"),
   (334, "yyxyxyxyyyxyxyx"), (335, "xyyxyyyxyx"), (336, "yxyyxyyyxyyyx"),
   (337, "xyxyyxyyyxyyyxyx"), (340, "yyyxyyyx"), (341, "xyxyyyyxyxyyxyx"), (342, "yyxyyyxyx"),
   (343, "yxyxyyxyyyyxyx"), (350, "yyyyyxyyxyyyyx"), (351, "yyxyxyx"), (352, "xyxyxyyyxyxyx"),
   (353, "xyxyyyxyyyyx"), (360, "xyyxyyyyyxyxyx"), (361, "xyxyxyyxyx"), (362, "yyyxyyxyyyyxyyyx"),
   (363, "yyxyyyxyxyyxyx"), (366, "yxyyxyx"), (367, "xyxyyyyyxyxyx"), (368, "xyyyxyyxyxyyyx"),
   (369, "yyyyxyyyx"), (372, "xyyyxyyxyyyx"), (373, "yyyxyyyxyx"), (374, "xyyxyyyyx"),
   (375, "yyyxyxyx"), (376, "yxyyyxyyxyyyx"), (377, "yyyyxyyyxyx"), (378, "yyxyyxyyyyx"),
   (379, "yyyyyxyxyx"), (380, "yxyyxyyyyx"), (381, "yyyyxyxyx"), (384, "xyyyxyyyxyyyxyx"),
   (385, "yyxyyyx"), (386, "xyyyxyyyyxyxyyxyx"), (387, "xyyxyyyxyyyx"), (390, "yyyxyxyyyx"),
   (391, "yxyyyxyyyyxyyyx"), (392, "xyxyyxyyyyxyx"), (393, "yxyyyxyx"), (406, "xyyyxyyyyx"),
   (407, "xyxyyyxyxyx"), (410, "xyyyyxyxyyyx"), (411, "yxyyxyyyxyxyx"), (420, "yxyxyyyxyx"),
   (421, "xyyxyyyyxyx"), (424, "yxyxyx"), (425, "yyyyxyyxyyyyx"), (438, "xyyxyyxyyyxyxyx"),
   (439, "yyxyyxyxyyyx"), (440, "yxyyyyxyx"), (441, "xyyyxyyyyyxyxyx"), (444, "yxyyyyx"),
   (445, "yyxyxyxyxyx"), (446, "yyxyyxyyyx"), (447, "xyxyyyyxyxyx"), (448, "yxyxyyyxyxyx"),
   (449, "yxyyyxyyyyx"), (456, "xyyyyxyyyx"), (457, "yyyxyyxyxyyyx"), (458, "xyyyxyyyxyx"),
   (459, "yyyxyyxyyyx"), (462, "yyxyyyyx"), (463, "xyyyxyxyx"), (464, "yxyxyyxyx"),
   (465, "yyxyyyyyxyxyx"), (468, "xyyxyyyxyxyyxyx"), (469, "xyyyxyyxyyyyxyyyx"), (470, "xyxyyxyx"),
   (471, "yxyyyyyxyxyx"), (472, "yyyyyxyxyyyyx"), (473, "xyyyyxyyyxyx"), (474, "xyxyyxyyyyx"),
   (475, "xyyyyxyxyx"), (476, "xyyxyyxyyyyx"), (477, "xyyyyyxyxyx"), (482, "xyyxyyyxyyyxyx"),
   (483, "xyyyyyxyyxyyyx"), (484, "yyyyyxyyxyyyx"), (485, "yyxyyyxyyyxyx"), (486, "yxyyyxyyyx"),
   (487, "yyxyyyyxyxyyxyx"), (488, "xyyxyxyxyx"), (489, "yxyxyxyyyxyxyx"), (490, "yxyxyxyyxyx"),
   (491, "xyyyyxyxyyxyx"), (494, "xyyyyxyxyyyyx"), (495, "xyxyyyyyxyyyx"), (496, "yyxyxyxyx"),
   (497, "yxyyyyyxyyyyx"), (500, "xyxyxyxyyxyx"), (501, "yyyyxyxyyxyx"), (502, "yxyyyyyxyyyx"),
   (503, "yyyyxyxyyyyx"), (510, "yyyyxyyxyyxyyyx"), (511, "yxyxyyxyyxyx")]

@[expose] def conjWord (k : Fin 512) : List Gen :=
  wordOfString ((List.lookup k.val conjTable).getD "")

@[expose] def uTable : List (Nat × Nat) :=
  [(0, 0), (1, 6), (6, 4), (7, 2), (24, 14), (25, 8), (30, 12), (31, 10), (160, 32), (161, 38),
   (166, 36), (167, 34), (184, 46), (185, 40), (190, 44), (191, 42), (320, 64), (321, 70),
   (326, 66), (327, 68), (344, 72), (345, 78), (350, 76), (351, 74), (480, 96), (481, 102),
   (486, 98), (487, 100), (504, 104), (505, 110), (510, 108), (511, 106)]

@[expose] def uIdx (k : Fin 512) : Fin 512 :=
  Fin.ofNat 512 ((List.lookup k.val uTable).getD 0)

@[expose] def rowsConj (k : Fin 512) : Array V4 := wordRows rowsX rowsY (conjWord k)

end CFSG.Sporadic.Th.Max3.InvRep
