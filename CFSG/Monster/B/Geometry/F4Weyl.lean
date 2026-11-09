module

public import CFSG.Monster.B.Geometry.F4WeylData
public import CFSG.LieType.Chevalley.BraidWalk
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.GroupActions.ExchangeMatsumoto

public section

namespace CFSG.Monster.B.Geometry

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk
open CFSG.GroupActions.Exchange

@[expose] def f4Get (l : List (List ℕ)) (k : ℕ) : ℕ := (l.getD (k / 34) []).getD (k % 34) 0

@[expose] def f4Digit (c j : ℕ) : ℕ := c / 64 ^ j % 64

@[expose] def f4Act (i : Fin Tag.F4.rank) (c : ℕ) : ℕ :=
  Tag.F4.rootCertificate.image (f4Digit c 0) i +
    64 * Tag.F4.rootCertificate.image (f4Digit c 1) i +
    4096 * Tag.F4.rootCertificate.image (f4Digit c 2) i +
    262144 * Tag.F4.rootCertificate.image (f4Digit c 3) i

@[expose] def f4Gen (n : ℕ) : Fin Tag.F4.rank := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

@[expose] def f4Code (k : ℕ) : ℕ := f4Get f4Codes k

@[expose] def f4DistOf (k : ℕ) : ℕ := f4Get f4Dist k

@[expose] def f4Parent (k : ℕ) : ℕ := f4Get f4Par k / 4

@[expose] def f4Next (k : ℕ) (i : Fin Tag.F4.rank) : ℕ := f4Get f4Clos k / 2048 ^ (i : ℕ) % 2048

@[expose] def f4CheckBase : Bool := f4Code 0 == 794688 && f4DistOf 0 == 0

theorem f4CheckBase_eq : f4CheckBase = true := by decide +kernel

@[expose] def f4CheckParents : Bool :=
  (List.range 1152).all fun k =>
    k == 0 || (decide (f4Parent k < k) &&
      f4Code k == f4Act (f4Gen (f4Get f4Par k)) (f4Code (f4Parent k)) &&
      f4DistOf k == f4DistOf (f4Parent k) + 1)

theorem f4CheckParents_eq : f4CheckParents = true := by decide +kernel

@[expose] def f4CheckClosure : Bool :=
  (List.range 1152).all fun k => (List.finRange Tag.F4.rank).all fun i =>
    decide (f4Next k i < 1152) && f4Code (f4Next k i) == f4Act i (f4Code k) &&
      decide (f4DistOf (f4Next k i) ≤ f4DistOf k + 1)

theorem f4CheckClosure_eq : f4CheckClosure = true := by decide +kernel

@[expose] def f4CheckCodes : Bool :=
  (List.range 1152).all fun k => decide (f4Code k < 64 ^ 4) &&
    ((List.range 4).all fun j => decide (f4Digit (f4Code k) j < 48))

theorem f4CheckCodes_eq : f4CheckCodes = true := by decide +kernel

@[expose] def f4Ord : List ℕ :=
  [150, 213, 1123, 123, 1113, 180, 33, 456, 23, 1017, 990, 411, 12, 970, 18, 900, 937, 862, 56, 534,
    41, 957, 924, 487, 1090, 600, 86, 1105, 107, 647, 203, 275, 723, 170, 678, 237, 1057, 521, 133,
    1078, 160, 568, 875, 793, 340, 913, 382, 835, 0, 824, 1, 738, 782, 693, 5, 646, 2, 889, 851,
    599, 14, 722, 8, 809, 767, 677, 1147, 249, 1144, 327, 287, 369, 1141, 192, 1135, 413, 225, 458,
    1120, 342, 1130, 262, 300, 384, 356, 443, 314, 536, 489, 398, 708, 615, 520, 753, 567, 662, 99,
    284, 1099, 78, 1084, 246, 60, 367, 1063, 45, 1042, 325, 93, 441, 72, 886, 848, 396, 27, 1026,
    999, 779, 37, 821, 142, 353, 806, 115, 764, 311, 1051, 690, 51, 1072, 66, 735, 1008, 612, 189,
    1035, 222, 659, 946, 705, 260, 979, 298, 750, 214, 288, 1139, 181, 1133, 250, 28, 1028, 38, 971,
    1001, 938, 61, 550, 46, 1065, 1044, 503, 1118, 694, 134, 1128, 161, 739, 94, 629, 73, 1018, 991,
    582, 1095, 616, 193, 1110, 226, 663, 276, 357, 810, 238, 768, 315, 948, 876, 427, 981, 472, 914,
    15, 551, 9, 958, 925, 504, 3, 901, 6, 822, 863, 780, 1138, 179, 1132, 248, 212, 286, 30, 630,
    20, 887, 849, 583, 1117, 505, 1127, 132, 159, 552, 274, 355, 631, 236, 584, 313, 1094, 429,
    1109, 191, 224, 474, 794, 706, 428, 836, 473, 751, 1151, 328, 1150, 414, 370, 459, 4, 902, 7,
    823, 864, 781, 16, 737, 10, 959, 926, 692, 1149, 263, 1146, 506, 301, 553, 31, 808, 21, 888,
    850, 766, 1137, 430, 1143, 343, 385, 475, 444, 537, 399, 632, 585, 490, 795, 707, 614, 837, 661,
    752, 148, 211, 1064, 121, 1043, 178, 97, 285, 1015, 76, 988, 247, 140, 354, 955, 113, 922, 312,
    201, 273, 884, 168, 846, 235, 935, 860, 49, 968, 64, 898, 1000, 777, 84, 1027, 105, 819, 947,
    703, 131, 980, 158, 748, 873, 791, 190, 911, 223, 833, 32, 457, 22, 1016, 989, 412, 1122, 122,
    149, 365, 1112, 323, 55, 535, 40, 807, 765, 488, 11, 969, 17, 736, 936, 691, 202, 439, 169, 719,
    674, 394, 85, 1104, 1089, 596, 106, 643, 1056, 517, 1077, 258, 296, 564, 874, 613, 341, 912,
    383, 660, 52, 1073, 1052, 867, 67, 905, 152, 371, 1124, 125, 1114, 329, 1091, 783, 88, 1106,
    109, 825, 100, 460, 1100, 79, 1085, 415, 1058, 709, 264, 1079, 302, 754, 143, 538, 116, 962,
    929, 491, 1009, 798, 344, 1036, 386, 840, 205, 445, 890, 172, 852, 400, 1148, 251, 1145, 330,
    289, 372, 13, 972, 19, 903, 939, 865, 1136, 601, 1142, 194, 227, 648, 34, 645, 24, 1019, 992,
    598, 1121, 522, 1131, 265, 303, 569, 57, 721, 42, 960, 927, 676, 877, 796, 519, 915, 566, 838,
    358, 446, 724, 316, 679, 401, 58, 368, 43, 956, 923, 326, 91, 442, 70, 885, 847, 397, 210, 283,
    1098, 177, 1083, 245, 272, 352, 804, 234, 762, 310, 25, 899, 35, 820, 861, 778, 1050, 688, 130,
    1071, 157, 733, 1007, 610, 188, 1034, 221, 657, 792, 704, 261, 834, 299, 749, 44, 1062, 59, 549,
    1041, 502, 92, 628, 71, 720, 675, 581, 26, 1025, 36, 644, 998, 597, 1097, 77, 98, 454, 1082,
    409, 141, 532, 114, 627, 580, 485, 50, 1070, 1049, 501, 65, 548, 1006, 425, 1033, 338, 380, 470,
    945, 518, 978, 426, 471, 565, 1003, 940, 87, 1030, 108, 973, 1054, 866, 135, 1075, 162, 904,
    215, 290, 1102, 182, 1087, 252, 1011, 797, 195, 1038, 228, 839, 151, 373, 1067, 124, 1046, 331,
    950, 878, 266, 983, 304, 916, 204, 447, 1020, 171, 993, 402, 277, 359, 961, 239, 928, 317, 29,
    1029, 39, 828, 1002, 786, 1140, 183, 216, 461, 1134, 416, 136, 1129, 1119, 695, 163, 740, 62,
    554, 47, 1066, 1045, 507, 1096, 617, 1111, 345, 387, 664, 95, 633, 74, 893, 855, 586, 949, 712,
    431, 982, 476, 757, 278, 539, 240, 811, 769, 492, 139, 533, 112, 805, 763, 486, 96, 455, 75,
    1014, 987, 410, 200, 440, 167, 717, 672, 395, 1061, 120, 147, 366, 1040, 324, 48, 967, 63, 734,
    934, 689, 83, 1024, 997, 594, 104, 641, 944, 515, 977, 259, 297, 562, 872, 611, 339, 910, 381,
    658, 53, 974, 68, 906, 941, 868, 1093, 784, 196, 1108, 229, 826, 291, 374, 1126, 253, 1116, 332,
    1060, 710, 267, 1081, 305, 755, 101, 462, 80, 1021, 994, 417, 879, 799, 346, 917, 388, 841, 144,
    540, 117, 963, 930, 493, 360, 448, 891, 318, 853, 403, 90, 1107, 1092, 603, 111, 650, 1125, 127,
    154, 555, 1115, 508, 54, 1074, 69, 741, 1053, 696, 81, 1101, 102, 649, 1086, 602, 1059, 524,
    1080, 432, 477, 571, 1010, 618, 1037, 523, 570, 665, 145, 725, 118, 812, 770, 680, 207, 634,
    174, 726, 681, 587, 199, 626, 166, 718, 673, 579, 271, 531, 233, 625, 578, 484, 119, 954, 146,
    547, 921, 500, 82, 897, 103, 642, 859, 595, 1013, 176, 209, 453, 986, 408, 129, 966, 933, 499,
    156, 546, 871, 423, 909, 337, 379, 468, 790, 516, 832, 424, 469, 563, 138, 1076, 1055, 697, 165,
    742, 89, 1031, 110, 827, 1004, 785, 1103, 185, 218, 463, 1088, 418, 1012, 619, 1039, 347, 389,
    666, 153, 556, 126, 1068, 1047, 509, 951, 711, 433, 984, 478, 756, 206, 635, 173, 892, 854, 588,
    280, 541, 242, 813, 771, 494, 351, 438, 309, 530, 483, 393, 270, 716, 232, 803, 761, 671, 208,
    640, 175, 883, 845, 593, 128, 818, 155, 732, 776, 687, 953, 244, 920, 322, 282, 364, 896, 187,
    858, 407, 220, 452, 789, 336, 831, 257, 295, 378, 702, 609, 514, 747, 561, 656, 198, 1032, 1005,
    605, 231, 652, 952, 526, 985, 434, 479, 573, 1069, 255, 293, 557, 1048, 510, 137, 975, 164, 743,
    942, 698, 880, 620, 918, 525, 572, 667, 184, 1022, 217, 651, 995, 604, 279, 727, 241, 814, 772,
    682, 362, 636, 320, 728, 683, 589, 437, 529, 392, 623, 576, 482, 350, 624, 308, 715, 670, 577,
    281, 545, 243, 802, 760, 498, 186, 731, 219, 639, 686, 592, 882, 321, 363, 451, 844, 406, 256,
    817, 775, 497, 294, 544, 701, 421, 746, 335, 377, 466, 608, 513, 422, 655, 467, 560, 881, 436,
    919, 349, 391, 481, 976, 269, 943, 512, 307, 559, 800, 713, 621, 842, 668, 758, 1023, 334, 996,
    420, 376, 465, 197, 907, 230, 829, 869, 787, 292, 744, 254, 964, 931, 699, 361, 815, 319, 894,
    856, 773, 450, 543, 405, 638, 591, 496, 714, 622, 528, 759, 575, 669, 801, 527, 843, 435, 480,
    574, 348, 908, 870, 606, 390, 653, 965, 419, 464, 558, 932, 511, 268, 830, 306, 745, 788, 700,
    375, 654, 333, 895, 857, 607, 449, 730, 404, 816, 774, 685, 542, 637, 495, 729, 684, 590]

@[expose] def f4SortedCodes : List ℕ → Bool
  | a :: b :: l => Nat.blt (f4Code a) (f4Code b) && f4SortedCodes (b :: l)
  | _ => true

theorem f4Ord_length : f4Ord.length = 1152 := by decide +kernel

theorem f4Ord_lt : (f4Ord.all fun k => Nat.blt k 1152) = true := by decide +kernel

theorem f4Ord_sorted : f4SortedCodes f4Ord = true := by decide +kernel

theorem f4SortedCodes_pairwise :
    ∀ l : List ℕ, f4SortedCodes l = true → l.Pairwise fun a b => f4Code a < f4Code b
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [f4SortedCodes, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := f4SortedCodes_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

theorem f4Ord_map_nodup : (f4Ord.map f4Code).Nodup :=
  List.pairwise_map.mpr ((f4SortedCodes_pairwise f4Ord f4Ord_sorted).imp ne_of_lt)

theorem mem_f4Ord {k : ℕ} (hk : k < 1152) : k ∈ f4Ord := by
  have hsub : f4Ord.toFinset ⊆ Finset.range 1152 := fun x hx => by
    have := List.all_eq_true.mp f4Ord_lt x (List.mem_toFinset.mp hx)
    rw [Nat.blt_eq] at this
    exact Finset.mem_range.mpr this
  have hcard : (Finset.range 1152).card ≤ f4Ord.toFinset.card := by
    rw [List.toFinset_card_of_nodup f4Ord_map_nodup.of_map, f4Ord_length, Finset.card_range]
  rw [← List.mem_toFinset, Finset.eq_of_subset_of_card_le hsub hcard]
  exact Finset.mem_range.mpr hk

theorem f4_roots_length : Tag.F4.rootCertificate.roots.length = 48 := by decide +kernel

theorem f4Code_zero : f4Code 0 = 794688 := by
  have h := f4CheckBase_eq
  simp only [f4CheckBase, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem f4DistOf_zero : f4DistOf 0 = 0 := by
  have h := f4CheckBase_eq
  simp only [f4CheckBase, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem f4_parent {k : ℕ} (hk : k < 1152) (hk0 : k ≠ 0) :
    f4Parent k < k ∧ f4Code k = f4Act (f4Gen (f4Get f4Par k)) (f4Code (f4Parent k)) ∧
      f4DistOf k = f4DistOf (f4Parent k) + 1 := by
  have h := f4CheckParents_eq
  simp only [f4CheckParents, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h k hk with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h hk0
  · exact ⟨h1, h2, h3⟩

theorem f4_next {k : ℕ} (hk : k < 1152) (i : Fin Tag.F4.rank) :
    f4Next k i < 1152 ∧ f4Code (f4Next k i) = f4Act i (f4Code k) ∧
      f4DistOf (f4Next k i) ≤ f4DistOf k + 1 := by
  have h := f4CheckClosure_eq
  simp only [f4CheckClosure, List.all_eq_true, List.mem_range, List.mem_finRange,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, true_implies] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk i
  exact ⟨h1, h2, h3⟩

theorem f4_code {k : ℕ} (hk : k < 1152) :
    f4Code k < 64 ^ 4 ∧ (∀ j < 4, f4Digit (f4Code k) j < 48) := by
  have h := f4CheckCodes_eq
  simp only [f4CheckCodes, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h k hk

theorem f4Digit_pack {a b c d : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64) :
    f4Digit (a + 64 * b + 4096 * c + 262144 * d) 0 = a ∧
      f4Digit (a + 64 * b + 4096 * c + 262144 * d) 1 = b ∧
      f4Digit (a + 64 * b + 4096 * c + 262144 * d) 2 = c ∧
      f4Digit (a + 64 * b + 4096 * c + 262144 * d) 3 = d := by
  simp only [f4Digit]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> omega

theorem eq_of_f4Digit_eq {c c' : ℕ} (hc : c < 64 ^ 4) (hc' : c' < 64 ^ 4)
    (h : ∀ j < 4, f4Digit c j = f4Digit c' j) : c = c' := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  simp only [f4Digit] at h0 h1 h2 h3
  norm_num at hc hc' h0 h1 h2 h3
  omega

theorem f4Digit_act
    (i : Fin Tag.F4.rank) {c : ℕ} (hc : ∀ j < 4, f4Digit c j < 48) {j : ℕ}
    (hj : j < 4) :
    f4Digit (f4Act i c) j = Tag.F4.rootCertificate.image (f4Digit c j) i := by
  have himg : ∀ j < 4, Tag.F4.rootCertificate.image (f4Digit c j) i < 64 := fun j hj => by
    have := rootCertificate_image_lt (τ := .F4) (by rw [f4_roots_length]; exact hc j hj) i
    rw [f4_roots_length] at this
    omega
  obtain ⟨e0, e1, e2, e3⟩ := f4Digit_pack (himg 0 (by norm_num)) (himg 1 (by norm_num))
    (himg 2 (by norm_num)) (himg 3 (by norm_num))
  unfold f4Act
  interval_cases j
  · exact e0
  · exact e1
  · exact e2
  · exact e3

@[expose] def F4Realizes
    (w : WeylGroup .F4) (c : ℕ) : Prop :=
  ∀ j : Fin Tag.F4.rank, f4Digit c j < 48 ∧
    w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = Tag.F4.rootCertificate.root (f4Digit c j)

theorem f4Realizes_one :
    F4Realizes 1 794688 := by
  intro j
  have hd : f4Digit 794688 j = j := by
    fin_cases j <;> decide
  rw [hd, one_smul, (rootCertificate_basis_table (τ := .F4)).2.1 j]
  exact ⟨by fin_cases j <;> decide, rfl⟩

theorem F4Realizes.digit_lt
    {w : WeylGroup .F4} {c : ℕ} (h : F4Realizes w c) :
    ∀ j < 4, f4Digit c j < 48 := fun j hj => (h ⟨j, hj⟩).1

theorem F4Realizes.simple_mul
    {w : WeylGroup .F4} {c : ℕ} (h : F4Realizes w c)
    (i : Fin Tag.F4.rank) : F4Realizes (simple .F4 i * w) (f4Act i c) := by
  intro j
  have hj : (j : ℕ) < 4 := j.2
  rw [f4Digit_act i h.digit_lt hj]
  have hlt : f4Digit c j < Tag.F4.rootCertificate.roots.length := by
    rw [f4_roots_length]; exact (h j).1
  refine ⟨?_, ?_⟩
  · have := rootCertificate_image_lt hlt i
    rwa [f4_roots_length] at this
  · rw [mul_smul, (h j).2, simple_smul, rootCertificate_root_image hlt]

theorem F4Realizes.eq
    {w w' : WeylGroup .F4} {c : ℕ} (h : F4Realizes w c)
    (h' : F4Realizes w' c) : w = w' :=
  ext_single fun j => (h j).2.trans (h' j).2.symm

theorem F4Realizes.code_eq
    {w : WeylGroup .F4} {c c' : ℕ} (h : F4Realizes w c)
    (h' : F4Realizes w c') (hc : c < 64 ^ 4) (hc' : c' < 64 ^ 4) : c = c' := by
  refine eq_of_f4Digit_eq hc hc' fun j hj => ?_
  have e := (h ⟨j, hj⟩).2.symm.trans (h' ⟨j, hj⟩).2
  exact rootCertificate_root_injOn (by rw [f4_roots_length]; exact (h ⟨j, hj⟩).1)
    (by rw [f4_roots_length]; exact (h' ⟨j, hj⟩).1) e

@[expose] def f4WordAux : ℕ → ℕ → List (Fin Tag.F4.rank)
  | 0, _ => []
  | n + 1, k => if k = 0 then [] else f4Gen (f4Get f4Par k) :: f4WordAux n (f4Parent k)

@[expose] def f4Word (k : ℕ) : List (Fin Tag.F4.rank) := f4WordAux (f4DistOf k) k

@[expose] noncomputable def f4Elem
    (k : ℕ) : WeylGroup .F4 :=
  (coxeterSystem .F4).wordProd (f4Word k)

theorem f4DistOf_pos {k : ℕ} (hk : k < 1152) (hk0 : k ≠ 0) : 0 < f4DistOf k := by
  have := (f4_parent hk hk0).2.2
  omega

theorem f4Realizes_wordAux :
    ∀ n k, k < 1152 → f4DistOf k = n →
    F4Realizes ((coxeterSystem .F4).wordProd (f4WordAux n k)) (f4Code k) ∧
      (f4WordAux n k).length = n := by
  intro n
  induction n with
  | zero =>
    intro k hk hd
    have hk0 : k = 0 := by
      by_contra hne
      have := f4DistOf_pos hk hne
      omega
    subst hk0
    rw [f4Code_zero]
    exact ⟨by simpa [f4WordAux] using f4Realizes_one, rfl⟩
  | succ n ih =>
    intro k hk hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [f4DistOf_zero] at hd
      omega
    obtain ⟨hp, hc, hdp⟩ := f4_parent hk hk0
    have IH := ih (f4Parent k) (by omega) (by omega)
    simp only [f4WordAux, hk0, ite_false, List.length_cons]
    refine ⟨?_, by rw [IH.2]⟩
    rw [CoxeterSystem.wordProd_cons]
    rw [hc]
    exact IH.1.simple_mul _

theorem f4Realizes_elem
    {k : ℕ} (hk : k < 1152) : F4Realizes (f4Elem k) (f4Code k) :=
  (f4Realizes_wordAux _ k hk rfl).1

theorem length_f4Word
    (k : ℕ) (hk : k < 1152) : (f4Word k).length = f4DistOf k :=
  (f4Realizes_wordAux _ k hk rfl).2

theorem exists_entry
    (w : WeylGroup .F4) :
    ∃ k < 1152, F4Realizes w (f4Code k) ∧ f4DistOf k ≤ (coxeterSystem .F4).length w := by
  induction h : (coxeterSystem .F4).length w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hw : w = 1
    · subst hw
      exact ⟨0, by norm_num, by rw [f4Code_zero]; exact f4Realizes_one,
        by rw [f4DistOf_zero]; omega⟩
    obtain ⟨i, hi⟩ := (coxeterSystem .F4).exists_leftDescent_of_ne_one hw
    have hl := (coxeterSystem .F4).isLeftDescent_iff.mp hi
    obtain ⟨k', hk', hr, hd⟩ := ih _ (by omega) ((coxeterSystem .F4).simple i * w) rfl
    obtain ⟨hn, hc, hdn⟩ := f4_next hk' i
    refine ⟨f4Next k' i, hn, ?_, by omega⟩
    rw [hc]
    have := hr.simple_mul i
    rwa [← mul_assoc, (coxeterSystem .F4).simple_mul_simple_self, one_mul] at this

theorem f4Code_injOn {k k' : ℕ} (hk : k < 1152) (hk' : k' < 1152) (h : f4Code k = f4Code k') :
    k = k' :=
  List.inj_on_of_nodup_map f4Ord_map_nodup (mem_f4Ord hk) (mem_f4Ord hk') h

theorem f4Elem_bijective :
    Function.Bijective fun k : Fin 1152 => f4Elem k := by
  refine ⟨fun k k' h => Fin.ext ?_, fun w => ?_⟩
  · have h1 := f4Realizes_elem k.2
    have h2 := f4Realizes_elem k'.2
    have h' : f4Elem k = f4Elem k' := h
    have h1' : F4Realizes (f4Elem k') (f4Code k) := h' ▸ h1
    exact f4Code_injOn k.2 k'.2 (h1'.code_eq h2 (f4_code k.2).1 (f4_code k'.2).1)
  · obtain ⟨k, hk, hr, -⟩ := exists_entry w
    exact ⟨⟨k, hk⟩, (f4Realizes_elem hk).eq hr⟩

theorem card_f4WeylGroup :
    Nat.card (WeylGroup .F4) = 1152 := by
  rw [← Nat.card_eq_of_bijective _ f4Elem_bijective, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isReduced_f4Word
    {k : ℕ} (hk : k < 1152) : (coxeterSystem .F4).IsReduced (f4Word k) := by
  obtain ⟨k', hk', hr, hd⟩ := exists_entry (f4Elem k)
  have hkk : k' = k := f4Code_injOn hk' hk
    (hr.code_eq (f4Realizes_elem hk) (f4_code hk').1 (f4_code hk).1)
  subst hkk
  have hle := (coxeterSystem .F4).length_wordProd_le (f4Word k')
  rw [CoxeterSystem.IsReduced]
  change (coxeterSystem .F4).length (f4Elem k') = _
  rw [length_f4Word k' hk] at hle ⊢
  exact le_antisymm hle hd

theorem sum_f4
    {β : Type*} [AddCommMonoid β] (f : WeylGroup .F4 → β) :
    ∑ᶠ w, f w = ∑ k : Fin 1152, f (f4Elem k) := by
  rw [← finsum_eq_sum_of_fintype]
  exact (finsum_comp_equiv (Equiv.ofBijective _ f4Elem_bijective)).symm

end CFSG.Monster.B.Geometry
