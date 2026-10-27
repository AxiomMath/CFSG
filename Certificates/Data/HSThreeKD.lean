module

public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Schreier.ClassSum
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public meta import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import CFSG.Sporadic.Schreier.Enumeration
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Sporadic.Schreier.ClassSum
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264HS

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev hsA : Equiv.Perm (Fin 100) :=
  List.formPerm [0, 1] * List.formPerm [2, 4] * List.formPerm [3, 6] * List.formPerm [7, 11] *
    List.formPerm [8, 13] * List.formPerm [9, 15] * List.formPerm [10, 14] *
    List.formPerm [12, 19] * List.formPerm [16, 24] * List.formPerm [17, 25] *
    List.formPerm [18, 27] * List.formPerm [20, 30] * List.formPerm [22, 32] *
    List.formPerm [23, 34] * List.formPerm [28, 40] * List.formPerm [29, 42] *
    List.formPerm [35, 47] * List.formPerm [36, 49] * List.formPerm [37, 51] *
    List.formPerm [38, 46] * List.formPerm [39, 53] * List.formPerm [43, 57] *
    List.formPerm [45, 48] * List.formPerm [52, 65] * List.formPerm [54, 67] *
    List.formPerm [55, 68] * List.formPerm [59, 70] * List.formPerm [60, 71] *
    List.formPerm [62, 74] * List.formPerm [63, 75] * List.formPerm [64, 76] *
    List.formPerm [66, 80] * List.formPerm [69, 83] * List.formPerm [78, 87] *
    List.formPerm [81, 91] * List.formPerm [82, 92] * List.formPerm [84, 89] *
    List.formPerm [85, 88] * List.formPerm [86, 90] * List.formPerm [95, 98]

abbrev hsB : Equiv.Perm (Fin 100) :=
  List.formPerm [0, 2, 5, 9, 16] * List.formPerm [1, 3, 7, 12, 20] *
    List.formPerm [4, 8, 14, 22, 33] * List.formPerm [6, 10, 17, 26, 38] *
    List.formPerm [11, 18, 28, 41, 56] * List.formPerm [13, 21, 31, 44, 59] *
    List.formPerm [15, 23, 35, 48, 63] * List.formPerm [19, 29, 30, 43, 58] *
    List.formPerm [24, 36, 50, 65, 79] * List.formPerm [25, 37, 52, 47, 62] *
    List.formPerm [27, 39, 54, 67, 81] * List.formPerm [32, 45, 60, 72, 53] *
    List.formPerm [34, 46, 61, 73, 86] * List.formPerm [40, 55, 69, 42, 57] *
    List.formPerm [49, 64, 77, 89, 83] * List.formPerm [51, 66, 76, 71, 85] *
    List.formPerm [68, 82, 93, 74, 87] * List.formPerm [70, 84, 94, 98, 78] *
    List.formPerm [75, 88, 95, 91, 97] * List.formPerm [80, 90, 96, 99, 92]

@[expose] def hsS : List (Equiv.Perm (Fin 100)) := [hsA, hsB]

@[expose] def zW : List Int :=
  [2, 2, 1, 2, 1, 2, 2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, 2, 2, -1, -2, 1, 2, 1, 2, 2, 1, 2,
  -1, 2, 2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2,
  -2, 1, 2, 2]

@[expose] def m1W : List Int :=
  [2, 2, 1, 2, 1, -2, -2, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, -2, -2, 1, 2,
  2, 1, 2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
  -2, -2, 1, 2, 2, 1, -2]

@[expose] def m2W : List Int :=
  [2, -1, -2, -1, 2, 2, 2, 1, -2, -2, 1, -2, 1, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, 2, 2, -1, -2, -1,
  2, -1, -2, -1, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, -1, -2, -2, -2, -1, 2, 2, -1, -2]

@[expose] def m3W : List Int :=
  [-2, -1, 2, 2, -1, 2, -1, 2, 2, -1, -2, -2, -1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -2,
  1, 2, 2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2]

@[expose] def hsMooreOK (_ : Unit := ()) : Bool :=
  let z := evalCodes hsS zW
  let m1 := evalCodes hsS m1W
  let m2 := evalCodes hsS m2W
  let m3 := evalCodes hsS m3W
  decide (z ^ 3 = 1) && decide (z ≠ 1) && decide (m1 ^ 3 = 1) && decide (m2 ^ 2 = 1) &&
    decide (m3 ^ 2 = 1) && decide ((m1 * m2) ^ 3 = 1) && decide ((m2 * m3) ^ 3 = 1) &&
    decide ((m1 * m3) ^ 2 = 1) && decide (m1 ≠ 1) && decide (m1 * z = z * m1) &&
    decide (m2 * z = z * m2) && decide (m3 * z = z * m3)

@[expose] def hsClassOK (_ : Unit := ()) : Bool :=
  let gens := pairTables hsA hsB
  let gensInv := pairTables hsA⁻¹ hsB⁻¹
  let x := toTable (evalCodes hsS zW)
  let C := conjClosure 100 gens gensInv x 130000
  conjTreeOK 100 gens gensInv x C.1 C.2.1 C.2.2 && keysDistinct 100 C.1.toList &&
    C.1.size == 123200

@[expose] def imgArr (g : Equiv.Perm (Fin 100)) : Array ℕ := Array.ofFn fun i => (g i : ℕ)

@[expose] def hsGensOK (_ : Unit := ()) : Bool :=
  siftA 100 hs100PLevels hs100BaseArr 0 (imgArr hsA) &&
    siftA 100 hs100PLevels hs100BaseArr 0 (imgArr hsB)

@[expose] def hsThreeOK (_ : Unit := ()) : Bool := hsGensOK () && hsMooreOK () && hsClassOK ()

end CFSG.LocalAnalysis.GLTheoremA.KD264HS
