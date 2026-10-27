module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.EvenSmallLie.OmegaEight CFSG.AGLEmbedding.KFactProofs.Fi22Five

set_option compiler.extract_closed false

@[expose] def ordList : List Nat :=
  [2525, 2628, 1022, 1866, 3453, 620, 535, 1113, 1139, 964, 3360, 2754, 1995, 457, 3041, 492, 3371,
   364, 793, 1009, 1365, 1439, 1790, 1531, 2746, 247, 1053, 1066, 275, 2827, 2073, 1440, 1212,
   3285, 2792, 3232, 1073, 2520, 2093, 86, 1010, 3417, 763, 668, 2880, 85, 1111, 154, 3314, 1271,
   2762, 3313, 3287, 2546, 2845, 2846, 2168, 401, 2575, 2347, 2996, 2475, 779, 162, 1045, 1003, 0,
   3432, 3055, 2576, 1870, 1889, 1897, 2557, 1297, 102, 2236, 232, 2569, 2363, 2393, 3507, 1263,
   2376, 3175, 2613, 1712, 2841, 2261, 1502, 441, 810, 890, 1807, 2409, 2481, 3428, 3176, 2385,
   1403, 1059, 3204, 2840, 1411, 2671, 500, 2110, 220, 559, 2969, 879, 3146, 936, 2933, 1532, 2298,
   1306, 3379, 3010, 719, 13, 2989, 1040, 2524, 2899, 172, 24, 1036, 1950, 2208, 3003, 333, 1342,
   3115, 2807, 991, 3201, 1646, 443, 2106, 1700, 58, 50, 2962, 1162, 2172, 1459, 3286, 894, 1672,
   2244, 2365, 184, 2056, 2439, 1713, 1923, 3124, 1096, 2743, 1692, 2212, 844, 471, 259, 1426,
   2178, 224, 2956, 204, 904, 3039, 1587, 2271, 3309, 2979, 263, 777, 585, 49, 1330, 2234, 1064,
   150, 949, 2015, 1269, 2563, 3305, 127, 1194, 2677, 2584, 771, 2077, 1967, 2790, 3247, 2716,
   2501, 3189, 2542, 2952, 1366, 2784, 846, 2302, 1018, 1679, 800, 1074, 481, 825, 185, 2074, 2096,
   1265, 1985, 2020, 2388, 2206, 2664, 255, 2030, 721, 3042, 1718, 77, 2013, 818, 1859, 602, 1517,
   3164, 536, 534, 491, 1641, 1282, 1383, 1431, 416, 2089, 2970, 3230, 440, 2606, 1474, 3294, 3190,
   854, 2972, 308, 2782, 2033, 3402, 720, 1809, 1858, 603, 2428, 683, 1526, 2582, 45, 341, 469,
   717, 1258, 2182, 65, 663, 1001, 20, 412, 1037, 3228, 3465, 1972, 1594, 3226, 2071, 1873, 1382,
   1688, 998, 2126, 1081, 523, 2767, 1422, 2548, 2211, 1926, 2507, 1143, 4, 1471, 563, 764, 2822,
   2783, 2995, 1078, 2224, 3276, 2567, 1355, 2526, 1637, 3128, 1728, 2405, 847, 2751, 2159, 939,
   921, 3330, 3078, 819, 1087, 1717, 78, 2336, 1482, 1142, 3368, 1574, 1163, 187, 1034, 711, 3283,
   704, 48, 2900, 262, 3447, 1953, 1590, 1189, 248, 1882, 752, 2149, 788, 240, 2444, 3094, 296,
   583, 3031, 2596, 332, 1786, 3152, 1425, 576, 329]

@[expose] def ordA : Array Nat := ordList.toArray

@[expose] def posA : Array Nat := Array.ofFn (n := 3510) fun p => ordList.idxOf p.val

@[expose] def resA (t : Array Nat) : Array Nat :=
  Array.ofFn (n := 360) fun j => posA[t[ordA[j.val]!]!]!

@[expose] def presOK (t : Array Nat) : Bool :=
  allLt 360 fun j => decide (posA[t[ordA[j]!]!]! < 360)

@[expose] def ordOK : Bool :=
  ordA.size == 360 && posA.size == 3510 &&
    allLt 360 (fun j => decide (ordA[j]! < 3510) && posA[ordA[j]!]! == j) &&
    allLt 3510 (fun p => !(decide (posA[p]! < 360)) || ordA[posA[p]!]! == p)

@[expose] def autBaseArr : Array Nat := (autBase.map Fin.val).toArray

@[expose] def inAutA (t : Array Nat) : Bool :=
  siftA 360 (rawLevels 360 autS autBaseArr) autBaseArr 0 t

@[expose] def planeFaithful : Bool :=
  allLt 5 fun i => allLt 5 fun j => (i == 0 && j == 0) ||
    !(eqA 360 (resA (planeA i j)) (idA 360))

@[noinline, expose] def d4Check : Bool :=
  ordOK && presOK g1A && presOK g2A && presOK n1A && presOK n2A && presOK zA &&
    allLt centClosure.1.size (fun i => presOK centClosure.1[i]!) &&
    inAutA (resA g1A) && inAutA (resA g2A) && planeFaithful && !(presOK (evalW [1]))

end CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4
