module

public import Lean.Data.Json.FromToJson.Basic
public import Lean.Data.Json.Parser

public section

namespace CFSG.Monster.B.Co2Catalog

open Lean (Json)

@[expose] def bridgeText : String :=
  "{\n\
  \x20 \"purpose\": \"Original exact native-to-catalog Co2 matrix bridge proposal; no independen\
  t review.\",\n\
  \x20 \"native_a_word\": [\n\
  \x20   15\n\
  \x20 ],\n\
  \x20 \"native_b_word\": [\n\
  \x20   -2,\n\
  \x20   -3,\n\
  \x20   -9,\n\
  \x20   -8,\n\
  \x20   -9,\n\
  \x20   -13,\n\
  \x20   -11,\n\
  \x20   -16,\n\
  \x20   -21,\n\
  \x20   -8,\n\
  \x20   -9,\n\
  \x20   -22,\n\
  \x20   -24,\n\
  \x20   -4,\n\
  \x20   -2,\n\
  \x20   -1,\n\
  \x20   2,\n\
  \x20   14,\n\
  \x20   2,\n\
  \x20   14,\n\
  \x20   14,\n\
  \x20   23,\n\
  \x20   2,\n\
  \x20   9,\n\
  \x20   9,\n\
  \x20   21,\n\
  \x20   24,\n\
  \x20   18,\n\
  \x20   17,\n\
  \x20   13,\n\
  \x20   5,\n\
  \x20   15,\n\
  \x20   2,\n\
  \x20   14,\n\
  \x20   2,\n\
  \x20   14,\n\
  \x20   14,\n\
  \x20   23,\n\
  \x20   2,\n\
  \x20   9,\n\
  \x20   9,\n\
  \x20   21,\n\
  \x20   24,\n\
  \x20   18,\n\
  \x20   17,\n\
  \x20   13,\n\
  \x20   5,\n\
  \x20   15,\n\
  \x20   2,\n\
  \x20   14,\n\
  \x20   2,\n\
  \x20   14,\n\
  \x20   14,\n\
  \x20   23,\n\
  \x20   2,\n\
  \x20   9,\n\
  \x20   9,\n\
  \x20   21,\n\
  \x20   24,\n\
  \x20   18,\n\
  \x20   17,\n\
  \x20   13,\n\
  \x20   5,\n\
  \x20   15,\n\
  \x20   1,\n\
  \x20   2,\n\
  \x20   4,\n\
  \x20   24,\n\
  \x20   22,\n\
  \x20   9,\n\
  \x20   8,\n\
  \x20   21,\n\
  \x20   16,\n\
  \x20   11,\n\
  \x20   13,\n\
  \x20   9,\n\
  \x20   8,\n\
  \x20   9,\n\
  \x20   3,\n\
  \x20   2\n\
  \x20 ],\n\
  \x20 \"native_rows\": [\n\
  \x20   [\n\
  \x20     12318,\n\
  \x20     12317,\n\
  \x20     4,\n\
  \x20     12311,\n\
  \x20     12303,\n\
  \x20     442400,\n\
  \x20     1800256,\n\
  \x20     454815,\n\
  \x20     747807,\n\
  \x20     455199,\n\
  \x20     748575,\n\
  \x20     1060891,\n\
  \x20     1058843,\n\
  \x20     1054747,\n\
  \x20     1079300,\n\
  \x20     1095684,\n\
  \x20     1128452,\n\
  \x20     1193988,\n\
  \x20     1325060,\n\
  \x20     1587204,\n\
  \x20     14363,\n\
  \x20     3160068\n\
  \x20   ],\n\
  \x20   [\n\
  \x20     1574232,\n\
  \x20     2813096,\n\
  \x20     786461,\n\
  \x20     2210002,\n\
  \x20     2317639,\n\
  \x20     1107934,\n\
  \x20     1472506,\n\
  \x20     1623393,\n\
  \x20     3233574,\n\
  \x20     145096,\n\
  \x20     1046142,\n\
  \x20     2147565,\n\
  \x20     1889377,\n\
  \x20     1070516,\n\
  \x20     3391670,\n\
  \x20     665745,\n\
  \x20     3025201,\n\
  \x20     1670464,\n\
  \x20     1890518,\n\
  \x20     3198194,\n\
  \x20     2410223,\n\
  \x20     3404192\n\
  \x20   ]\n\
  \x20 ],\n\
  \x20 \"catalog_transpose_rows\": [\n\
  \x20   [\n\
  \x20     2114050,\n\
  \x20     2114049,\n\
  \x20     1048584,\n\
  \x20     1048580,\n\
  \x20     415936,\n\
  \x20     3150720,\n\
  \x20     415888,\n\
  \x20     128,\n\
  \x20     3150496,\n\
  \x20     512,\n\
  \x20     1024,\n\
  \x20     2048,\n\
  \x20     4096,\n\
  \x20     3473408,\n\
  \x20     16384,\n\
  \x20     917504,\n\
  \x20     3416064,\n\
  \x20     131072,\n\
  \x20     262144,\n\
  \x20     425984,\n\
  \x20     1048576,\n\
  \x20     2097152\n\
  \x20   ],\n\
  \x20   [\n\
  \x20     2097280,\n\
  \x20     2097154,\n\
  \x20     2097283,\n\
  \x20     3047424,\n\
  \x20     2621572,\n\
  \x20     3014664,\n\
  \x20     655360,\n\
  \x20     2621584,\n\
  \x20     2883584,\n\
  \x20     3014688,\n\
  \x20     2228288,\n\
  \x20     2359552,\n\
  \x20     3015168,\n\
  \x20     2753536,\n\
  \x20     2361344,\n\
  \x20     3018752,\n\
  \x20     2097152,\n\
  \x20     2760704,\n\
  \x20     802816,\n\
  \x20     2621440,\n\
  \x20     2686976,\n\
  \x20     1048576\n\
  \x20   ]\n\
  \x20 ],\n\
  \x20 \"change_of_basis_rows\": [\n\
  \x20   2495974,\n\
  \x20   472725,\n\
  \x20   2177759,\n\
  \x20   823366,\n\
  \x20   3635269,\n\
  \x20   3623954,\n\
  \x20   5507,\n\
  \x20   2109435,\n\
  \x20   2710470,\n\
  \x20   1032327,\n\
  \x20   3267302,\n\
  \x20   1170103,\n\
  \x20   2972347,\n\
  \x20   2142667,\n\
  \x20   3505457,\n\
  \x20   3222369,\n\
  \x20   1270289,\n\
  \x20   3351486,\n\
  \x20   2379581,\n\
  \x20   2232114,\n\
  \x20   1774027,\n\
  \x20   24222\n\
  \x20 ],\n\
  \x20 \"intertwiner_dimension\": 1,\n\
  \x20 \"attempt\": 21\n\
  }\n"

structure BridgeFile where
  purpose : String
  nativeAWord : List Int
  nativeBWord : List Int
  nativeRows : List (List Nat)
  catalogTransposeRows : List (List Nat)
  changeOfBasisRows : List Nat
  intertwinerDimension : Nat
  attempt : Nat
  deriving DecidableEq, Inhabited

@[expose] def BridgeFile.ofJson (j : Json) : Except String BridgeFile := do
  pure
    { purpose := ← j.getObjValAs? String "purpose"
      nativeAWord := ← j.getObjValAs? (List Int) "native_a_word"
      nativeBWord := ← j.getObjValAs? (List Int) "native_b_word"
      nativeRows := ← j.getObjValAs? (List (List Nat)) "native_rows"
      catalogTransposeRows := ← j.getObjValAs? (List (List Nat)) "catalog_transpose_rows"
      changeOfBasisRows := ← j.getObjValAs? (List Nat) "change_of_basis_rows"
      intertwinerDimension := ← j.getObjValAs? Nat "intertwiner_dimension"
      attempt := ← j.getObjValAs? Nat "attempt" }

@[expose] def bridgeKeys : Except String (List String) := do
  let o ← (← Json.parse bridgeText).getObj?
  pure (o.toArray.map (·.1)).toList

@[expose] def bridgeFile : Except String BridgeFile := do
  BridgeFile.ofJson (← Json.parse bridgeText)

@[expose] def bridgeRec : BridgeFile where
  purpose := "Original exact native-to-catalog Co2 matrix bridge proposal; no independent review."
  nativeAWord := [15]
  nativeBWord := [-2, -3, -9, -8, -9, -13, -11, -16, -21, -8, -9, -22, -24, -4, -2, -1, 2, 14, 2,
    14, 14, 23, 2, 9, 9, 21, 24, 18, 17, 13, 5, 15, 2, 14, 2, 14, 14, 23, 2, 9, 9, 21, 24, 18, 17,
    13, 5, 15, 2, 14, 2, 14, 14, 23, 2, 9, 9, 21, 24, 18, 17, 13, 5, 15, 1, 2, 4, 24, 22, 9, 8, 21,
    16, 11, 13, 9, 8, 9, 3, 2]
  nativeRows :=
    [[12318, 12317, 4, 12311, 12303, 442400, 1800256, 454815, 747807, 455199, 748575, 1060891,
      1058843, 1054747, 1079300, 1095684, 1128452, 1193988, 1325060, 1587204, 14363, 3160068],
     [1574232, 2813096, 786461, 2210002, 2317639, 1107934, 1472506, 1623393, 3233574, 145096,
      1046142, 2147565, 1889377, 1070516, 3391670, 665745, 3025201, 1670464, 1890518, 3198194,
      2410223, 3404192]]
  catalogTransposeRows :=
    [[2114050, 2114049, 1048584, 1048580, 415936, 3150720, 415888, 128, 3150496, 512, 1024, 2048,
      4096, 3473408, 16384, 917504, 3416064, 131072, 262144, 425984, 1048576, 2097152],
     [2097280, 2097154, 2097283, 3047424, 2621572, 3014664, 655360, 2621584, 2883584, 3014688,
      2228288, 2359552, 3015168, 2753536, 2361344, 3018752, 2097152, 2760704, 802816, 2621440,
      2686976, 1048576]]
  changeOfBasisRows := [2495974, 472725, 2177759, 823366, 3635269, 3623954, 5507, 2109435,
    2710470, 1032327, 3267302, 1170103, 2972347, 2142667, 3505457, 3222369, 1270289, 3351486,
    2379581, 2232114, 1774027, 24222]
  intertwinerDimension := 1
  attempt := 21

end CFSG.Monster.B.Co2Catalog
