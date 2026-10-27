module

public import Certificates.Data.Item434SporGenKit
public import CFSG.RankThree.Native.HSMcLSmallData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public import Certificates.Data.K426McL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (xArr zArr)

@[expose] def hsSigArrs : Array (Array ℕ) :=
  #[
    #[1, 0, 54, 47, 67, 21, 35, 63, 62, 34, 81, 75, 20, 74, 91, 23, 38, 28, 71, 30, 27, 5, 7, 8,
    46, 40, 99, 60, 25, 82, 18, 77, 11, 93, 13, 95, 14, 70, 24, 53, 17, 31, 92, 2, 97, 48, 16,
    98, 45, 10, 61, 59, 6, 39, 64, 69, 72, 4, 41, 86, 12, 50, 15, 85, 43, 3, 80, 76, 83, 42, 90,
    19, 56, 94, 9, 88, 57, 58, 51, 33, 66, 89, 68, 29, 36, 22, 78, 37, 32, 49, 87, 84, 55, 96,
    73, 52, 79, 44, 65, 26],
    #[52, 13, 11, 22, 23, 33, 9, 7, 57, 6, 24, 2, 86, 1, 97, 66, 61, 99, 18, 31, 20, 90, 3, 4,
    10, 29, 83, 94, 82, 25, 41, 19, 39, 5, 34, 74, 36, 93, 81, 32, 40, 30, 44, 75, 42, 63, 46,
    85, 65, 50, 49, 51, 0, 64, 54, 91, 71, 8, 72, 73, 78, 16, 62, 45, 53, 48, 15, 67, 68, 69,
    70, 56, 58, 59, 35, 43, 80, 77, 60, 79, 76, 38, 28, 26, 92, 47, 12, 96, 88, 89, 21, 55, 84,
    37, 27, 95, 87, 14, 98, 17],
    #[34, 61, 42, 96, 52, 17, 30, 22, 36, 47, 2, 75, 13, 12, 68, 49, 59, 62, 73, 11, 33, 1, 48,
    79, 64, 26, 77, 14, 15, 86, 6, 84, 57, 20, 0, 7, 51, 63, 83, 88, 8, 50, 58, 28, 82, 19, 21,
    9, 35, 43, 80, 40, 94, 85, 27, 31, 44, 32, 10, 98, 91, 46, 97, 37, 60, 89, 56, 4, 54, 99,
    39, 76, 93, 90, 25, 45, 53, 74, 55, 69, 92, 16, 66, 38, 78, 71, 65, 18, 95, 29, 87, 24, 41,
    72, 67, 70, 3, 5, 81, 23]]

@[expose] def hsE1 : Array ℕ :=
  #[0, 1, 87, 83, 48, 50, 13, 25, 55, 6, 90, 49, 47, 9, 99, 98, 75, 80, 60, 15, 3, 21, 26, 65,
    10, 94, 67, 69, 59, 27, 12, 66, 37, 96, 34, 74, 31, 93, 33, 39, 78, 76, 18, 16, 40, 28, 46,
    30, 77, 81, 53, 84, 35, 5, 79, 82, 51, 63, 73, 45, 42, 61, 92, 72, 2, 68, 36, 22, 23, 29, 70,
    62, 57, 91, 52, 43, 97, 4, 44, 89, 85, 11, 8, 20, 56, 17, 14, 64, 88, 54, 24, 58, 71, 32, 7,
    95, 38, 41, 19, 86]

@[expose] def hsE2 : Array ℕ :=
  #[0, 1, 96, 60, 25, 50, 6, 51, 82, 9, 43, 87, 30, 13, 76, 83, 32, 14, 98, 3, 18, 61, 78, 29,
    75, 84, 44, 71, 91, 92, 47, 22, 90, 49, 34, 35, 67, 24, 11, 21, 36, 85, 15, 93, 66, 73, 88,
    12, 94, 64, 53, 77, 52, 5, 79, 8, 48, 28, 63, 58, 19, 39, 68, 59, 33, 27, 26, 40, 69, 62, 46,
    65, 45, 72, 74, 37, 17, 7, 31, 89, 99, 2, 55, 42, 4, 86, 41, 38, 70, 54, 16, 57, 23, 10, 56,
    95, 81, 80, 20, 97]

@[expose] def hsOrds : List ℕ := [4, 2, 4]

@[expose] def hsPExps : List (ℕ × ℕ) := [(0, 1), (0, 1), (1, 0)]

@[expose] def hsWords : List (List ℤ) :=
  [[-1, -1], [-3, -3], [-4, -5, -1, -2, 1, 3], [-4, 6, 4, -6, 4], [-6, -6, -7, -6, 7, 6], [-6,
    -6, 8, 6, 6], [-8, -9, -8, -4, 9, 4], [-6, -7, -10, 7, 9, 6], [11, 9, 8]]

@[expose] def hsGenS : Array (Array ℕ) := pushWords 100 hsSigArrs hsWords

@[expose] def hsBase : List (Fin 100) := [0, 2, 1, 3, 4]

@[expose] def hsLevels : Array Level := rawLevels 100 hsGenS (hsBase.map Fin.val).toArray

@[expose] def hsChainCheck : Bool :=
  rawChainOK 100 (hsGenS.extract 0 3) hsGenS (hsBase.map Fin.val).toArray (wordsOf 3 hsWords)
      4 &&
    rawOrbitSizes 100 hsGenS (hsBase.map Fin.val).toArray == [100, 77, 60, 12, 8]

@[expose] def hsSiftCheck : Bool :=
  isInvA 100 (CFSG.RankThree.Native.hs100Arr 0) (invCand 100 (CFSG.RankThree.Native.hs100Arr 0)) &&
    isInvA 100 (CFSG.RankThree.Native.hs100Arr 1)
      (invCand 100 (CFSG.RankThree.Native.hs100Arr 1)) &&
    siftA 100 hsLevels (hsBase.map Fin.val).toArray 0 (CFSG.RankThree.Native.hs100Arr 0) &&
    siftA 100 hsLevels (hsBase.map Fin.val).toArray 0 (CFSG.RankThree.Native.hs100Arr 1) &&
    siftA 100 hsLevels (hsBase.map Fin.val).toArray 0 hsE1 &&
    siftA 100 hsLevels (hsBase.map Fin.val).toArray 0 hsE2

@[expose] def hsEltCheck : Bool :=
  e9Check 100 hsE1 hsE2 && sigCheck 100 hsSigArrs hsOrds hsPExps hsE1 hsE2

@[expose] def j2SigArrs : Array (Array ℕ) :=
  #[
    #[108, 163, 91, 1, 314, 41, 201, 7, 95, 162, 19, 289, 248, 74, 84, 24, 235, 82, 54, 214,
    120, 85, 15, 137, 45, 242, 65, 69, 100, 71, 312, 0, 32, 151, 34, 251, 130, 98, 62, 16, 154,
    258, 169, 27, 166, 22, 279, 262, 153, 187, 50, 226, 283, 36, 294, 207, 118, 12, 222, 40,
    157, 186, 38, 273, 290, 204, 4, 135, 199, 148, 237, 183, 93, 25, 21, 9, 99, 268, 233, 192,
    90, 127, 213, 313, 188, 13, 97, 96, 86, 39, 302, 81, 209, 270, 232, 152, 76, 216, 284, 87,
    165, 247, 276, 5, 311, 227, 78, 288, 309, 205, 55, 241, 29, 250, 263, 49, 64, 252, 260, 297,
    48, 292, 212, 208, 220, 138, 196, 2, 219, 269, 200, 240, 228, 287, 265, 133, 224, 126, 44,
    33, 26, 277, 189, 37, 305, 275, 185, 77, 43, 301, 14, 180, 308, 20, 218, 193, 173, 239, 147,
    238, 168, 259, 175, 178, 176, 243, 125, 225, 142, 61, 291, 121, 60, 156, 194, 75, 206, 177,
    3, 191, 139, 310, 271, 112, 10, 203, 42, 281, 150, 160, 68, 215, 136, 102, 101, 56, 23, 104,
    197, 272, 53, 161, 106, 254, 140, 141, 298, 249, 181, 114, 144, 293, 70, 306, 184, 230, 88,
    231, 59, 105, 117, 66, 167, 280, 79, 58, 170, 128, 83, 217, 179, 286, 211, 202, 234, 89, 18,
    122, 63, 172, 46, 129, 307, 28, 80, 245, 267, 174, 256, 110, 149, 223, 124, 304, 146, 257,
    57, 246, 103, 6, 195, 303, 182, 92, 11, 300, 171, 255, 158, 111, 282, 47, 190, 159, 278,
    261, 155, 109, 30, 131, 35, 115, 72, 107, 143, 134, 229, 67, 52, 295, 299, 51, 266, 94, 236,
    264, 210, 253, 164, 116, 285, 113, 244, 145, 119, 296, 17, 73, 8, 31, 123, 198, 274, 132,
    221],
    #[97, 304, 270, 209, 264, 108, 139, 170, 205, 285, 11, 122, 9, 288, 163, 145, 89, 52, 119,
    46, 66, 265, 39, 310, 43, 84, 18, 218, 291, 134, 158, 300, 183, 255, 204, 120, 110, 272, 59,
    94, 148, 8, 162, 249, 212, 179, 243, 261, 197, 167, 45, 113, 294, 275, 165, 69, 61, 292,
    314, 47, 147, 192, 53, 279, 188, 254, 283, 193, 161, 303, 54, 268, 185, 107, 155, 208, 135,
    152, 299, 171, 32, 236, 222, 13, 297, 79, 29, 274, 189, 182, 169, 176, 201, 65, 130, 245, 6,
    168, 276, 258, 149, 248, 129, 253, 278, 226, 127, 214, 44, 282, 173, 223, 10, 96, 260, 35,
    194, 106, 30, 172, 128, 1, 309, 199, 80, 83, 289, 295, 151, 103, 271, 5, 123, 4, 109, 63,
    159, 124, 102, 51, 125, 19, 202, 175, 95, 36, 92, 280, 211, 302, 263, 115, 213, 242, 230,
    73, 62, 71, 306, 2, 186, 49, 132, 17, 117, 33, 198, 224, 87, 296, 210, 284, 216, 15, 190,
    239, 60, 187, 277, 191, 246, 133, 235, 137, 67, 301, 111, 116, 234, 20, 217, 232, 81, 99,
    313, 256, 136, 98, 240, 42, 16, 58, 100, 150, 174, 28, 104, 24, 72, 31, 126, 154, 131, 23,
    74, 207, 26, 34, 55, 118, 105, 237, 231, 286, 68, 233, 195, 290, 267, 48, 40, 78, 50, 12,
    37, 200, 56, 57, 252, 101, 153, 180, 166, 307, 76, 238, 21, 298, 143, 215, 311, 287, 144,
    138, 227, 70, 220, 181, 184, 305, 90, 293, 156, 247, 257, 241, 178, 206, 259, 281, 196, 22,
    64, 221, 0, 262, 229, 251, 228, 244, 91, 25, 86, 88, 312, 225, 160, 266, 140, 7, 93, 41,
    273, 38, 14, 164, 114, 269, 203, 82, 308, 75, 142, 27, 250, 157, 219, 141, 3, 112, 77, 121,
    85, 177, 146],
    #[165, 189, 139, 307, 233, 161, 57, 208, 244, 96, 122, 211, 135, 18, 306, 15, 16, 250, 13,
    55, 171, 68, 310, 145, 212, 34, 154, 27, 251, 130, 182, 275, 210, 312, 25, 166, 298, 53,
    255, 172, 40, 157, 82, 138, 221, 45, 67, 47, 73, 279, 246, 273, 179, 37, 72, 19, 158, 6,
    234, 238, 71, 90, 62, 198, 243, 205, 103, 46, 21, 224, 81, 60, 54, 48, 218, 235, 105, 309,
    129, 128, 95, 70, 42, 173, 229, 176, 213, 159, 265, 256, 61, 207, 137, 108, 94, 80, 9, 297,
    202, 141, 133, 151, 266, 66, 111, 76, 114, 116, 93, 125, 110, 104, 263, 142, 106, 284, 107,
    296, 192, 152, 286, 186, 10, 174, 292, 109, 195, 274, 79, 78, 29, 258, 257, 100, 150, 12,
    143, 92, 43, 2, 288, 99, 113, 136, 169, 23, 225, 226, 282, 245, 134, 101, 119, 253, 26, 242,
    289, 41, 56, 87, 167, 5, 290, 305, 268, 0, 35, 160, 178, 144, 183, 20, 39, 83, 123, 196, 85,
    237, 168, 52, 214, 278, 30, 170, 194, 276, 121, 204, 217, 1, 248, 287, 118, 231, 184, 126,
    175, 223, 63, 299, 200, 260, 98, 216, 187, 65, 240, 91, 7, 269, 32, 11, 24, 86, 180, 314,
    203, 188, 74, 277, 302, 44, 304, 197, 69, 146, 147, 239, 295, 84, 230, 193, 232, 4, 58, 75,
    280, 177, 59, 227, 206, 283, 155, 64, 8, 149, 50, 271, 190, 249, 17, 28, 300, 153, 308, 38,
    89, 132, 131, 270, 201, 311, 262, 112, 267, 88, 102, 264, 164, 209, 259, 247, 291, 51, 127,
    31, 185, 219, 181, 49, 236, 294, 148, 241, 115, 301, 120, 191, 140, 156, 162, 272, 124, 313,
    281, 228, 117, 97, 36, 199, 252, 285, 220, 303, 222, 163, 14, 3, 254, 77, 22, 261, 33, 293,
    215]]

@[expose] def j2Ords : List ℕ := [4, 5, 2]

@[expose] def j2PExps : List (ℕ × ℕ) := [(1, 0), (1, 0), (0, 1)]

@[expose] def j2Words : List (List ℤ) :=
  [[2, 1, 3, 2, 3], [-3, -4, -1, 2, 1], [-5, 4, 5], [-4, -5, 6, 4], [-7, -7, -6, -7]]

@[expose] def j2GenS : Array (Array ℕ) := pushWords 315 j2SigArrs j2Words

@[expose] def j2Base : List (Fin 315) := [0, 3, 1, 2]

@[expose] def j2Levels : Array Level := rawLevels 315 j2GenS (j2Base.map Fin.val).toArray

@[expose] def j2ChainCheck : Bool :=
  rawChainOK 315 (j2GenS.extract 0 3) j2GenS (j2Base.map Fin.val).toArray (wordsOf 3 j2Words)
      4 &&
    rawOrbitSizes 315 j2GenS (j2Base.map Fin.val).toArray == [315, 32, 20, 3]

@[expose] def j2SiftCheck : Bool :=
  siftA 315 j2Levels (j2Base.map Fin.val).toArray 0
      CFSG.ComponentClassification.J2Cover.autStrong[0]! &&
    siftA 315 j2Levels (j2Base.map Fin.val).toArray 0
      CFSG.ComponentClassification.J2Cover.autStrong[1]! &&
    siftA 315 j2Levels (j2Base.map Fin.val).toArray 0 zArr &&
    siftA 315 j2Levels (j2Base.map Fin.val).toArray 0 xArr

@[expose] def j2EltCheck : Bool :=
  e9Check 315 zArr xArr && sigCheck 315 j2SigArrs j2Ords j2PExps zArr xArr

@[expose] def conjN (n : ℕ) (q t : Array ℕ) : Array ℕ := compA n (compA n q t) (invCand n q)

@[expose] def mclSift (x : Array ℕ) : Bool :=
  isInvA 275 x (invCand 275 x) &&
    siftA 275 CFSG.Sporadic.Schreier.PairMcL.levels CFSG.Sporadic.Schreier.PairMcL.baseArr 0 x

@[expose] def mclHex : String := include_str "Item434SporGenMcL.txt"

@[expose, irreducible] def mclArr (k : ℕ) : Array ℕ := hexTable 3 275 (275 * k) mclHex

@[expose] def mclDProd (u : ℕ) : Array ℕ :=
  compA 275 (compA 275 (compA 275 (powN 275 (mclArr 0) (u % 3))
    (powN 275 (mclArr 1) (u / 3 % 3))) (powN 275 (mclArr 2) (u / 9 % 3)))
    (powN 275 (mclArr 3) (u / 27 % 3))

@[expose] def mclInD (x : Array ℕ) : Bool := (List.range 81).any fun u => eqA 275 x (mclDProd u)

@[expose] def mclZCheck : Bool :=
  eqA 275 (mclArr 0) (idA 275) == false &&
    allLt CFSG.RankThree.PartTwo.KFacts.K426.mcl3QGens.size
      (fun k => commN 275 (mclArr 0) CFSG.RankThree.PartTwo.KFacts.K426.mcl3QGens[k]!)

@[expose] def mclDCheck : Bool :=
  allLt 4 (fun k => mclSift (mclArr k)) &&
    allLt 4 (fun k => eqA 275 (powN 275 (mclArr k) 3) (idA 275)) &&
    allLt 4 (fun k => allLt 4 fun l => commN 275 (mclArr k) (mclArr l)) &&
    allLt 81 (fun u => allLt 81 fun v => u == v || !eqA 275 (mclDProd u) (mclDProd v))

@[expose] def mclLineCheck : Bool :=
  allLt 148 fun j =>
    mclInD CFSG.RankThree.PartTwo.KFacts.K426.mcl3Lines[j]! ||
      (List.range CFSG.RankThree.PartTwo.KFacts.K426.mcl3QCert.pts.size).any fun k =>
        let q := CFSG.RankThree.PartTwo.KFacts.K426.mcl3QCert.pts[k]!
        (List.range 24).any (fun i => eqA 275
          (conjN 275 q CFSG.RankThree.PartTwo.KFacts.K426.mcl3Lines[j]!) (mclArr (4 + i))) &&
          eqA 275 (conjN 275 q (mclArr 0)) (mclArr 0) && mclSift q

@[expose] def mclConjCheck : Bool :=
  allLt 24 fun i =>
    mclSift (mclArr (28 + i)) && isInvA 275 (mclArr (4 + i)) (invCand 275 (mclArr (4 + i))) &&
      mclInD (conjN 275 (mclArr (28 + i)) (mclArr (4 + i))) &&
      mclInD (conjN 275 (mclArr (28 + i)) (mclArr 0))

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
