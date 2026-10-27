module

public import CFSG.Sporadic.Schreier.RuCore

public section

namespace CFSG.Sporadic.RuSchreier

@[expose] def ru4060Text : String := include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ru4060.txt"

@[expose] def ru1920Text : String := include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ru1920.txt"

@[expose] def ru80Text : String := include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ru80.txt"

@[expose] def ruPtsText : String := include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ruPts.txt"

@[expose] def ruTreeText0 : String := include_str "../../../Certificates/Kernel/SporSch/Ru/data/ruTree-c0.txt"

@[expose] def ruTreeText1 : String := include_str "../../../Certificates/Kernel/SporSch/Ru/data/ruTree-c1.txt"

@[expose] def ruTreeText2 : String := include_str "../../../Certificates/Kernel/SporSch/Ru/data/ruTree-c2.txt"

@[expose] def ruTreeText3 : String := include_str "../../../Certificates/Kernel/SporSch/Ru/data/ruTree-c3.txt"

@[expose] def ruTreeText4 : String := include_str "../../../Certificates/Kernel/SporSch/Ru/data/ruTree-c4.txt"

@[expose] def ruTreeText5 : String := include_str "../../../Certificates/Kernel/SporSch/Ru/data/ruTree-c5.txt"

@[expose] def ruTreeText : String :=
  ruTreeText0 ++ ruTreeText1 ++ ruTreeText2 ++ ruTreeText3 ++ ruTreeText4 ++ ruTreeText5

@[expose] def ruSigmaText : String := include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ruSigma.txt"

@[expose] def ruLines4060 : List (ℕ × ℕ) := [(0, 2), (2, 7), (9, 6), (15, 18), (33, 6), (39, 6)]

@[expose] def ruLines1920 : List (ℕ × ℕ) := [(0, 7), (7, 7), (14, 10), (24, 10), (34, 7)]

@[expose] def ruPtsOffsets : List (ℕ × ℕ) :=
  [(0, 1920), (1920, 2048), (3968, 80), (4048, 12), (4060, 3584), (7644, 448), (8092, 28),
    (8120, 1920), (10040, 80)]

@[expose] def ruCProg : List SlotRow :=
  [
    .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .iv 5 6, .mu 6 1 9,
    .mu 9 5 10, .mu 3 8 1, .pwr 10 1 9, .mu 9 10 8, .pwr 6 8 11, .mu 7 7 8, .iv 8 7,
    .mu 7 10 6, .mu 6 8 10, .mu 9 10 8, .pwr 4 8 12, .mu 11 12 2]

@[expose] def ruNProg : List SlotRow :=
  [
    .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 5 8, .mu 2 2 1, .pwr 5 8 2, .iv 6 7,
    .mu 7 2 4, .mu 4 6 2, .mu 3 8 9, .mu 9 9 8, .iv 8 7, .mu 7 1 3, .mu 3 8 1]

@[expose] def ruNCenterWord : List ℤ :=
  [
    1, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, -2, 1, -2, -2, 1, -2,
    1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2,
    1, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, -2, 1, -2, 1, 2, 1,
    2, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, -2, 1, -2, 1, 2, 1,
    2, -2, 1, -2, 1, 2, 1, 2, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 1, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2,
    1, 2, 1, 2, 1, 2, 2, 1, 2, -2, 1, -2, 1, 2, 1, 2, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2,
    1, 2, 1, 2, 1, 2, 2, 1, 2]

@[expose] def ruSeedWord : List ℤ :=
  [2, 1]

@[expose] def ruOddProductOrder : ℕ :=
  7

@[expose] def ruSWords : List (List ℤ) :=
  [
    [-2, -2, 1, 2, 2], [-1, -2, -2, 1, 2, 2, 1], [-1, -2, -1, -2, 1, 2, 1, 2, 1],
    [-2, -1, -2, -1, -2, -1, 2, 1, 2, 2, 1, 2]]

@[expose] def ruKWords : List (List ℤ) :=
  [
    [-2, -2, -1, -2, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1],
    [-2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1],
    [-2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2],
    [-1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1],
    [-2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2],
    [-1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1],
    [-1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1,
      2],
    [-2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] def ruJWords : List (List ℤ) :=
  [
    [2, 2], [-1, 2, 2, 1], [-1, -1, 2, 2, 1, 1], [-2, -1, 2, 2, 1, 2], [1, 1, 1, 1, 1],
    [-1, -1, -1, 2, 2, 1, 1, 1]]

@[expose] def ruRWords : List (List ℤ) :=
  [
    [-1, -3, 1, 3], [-1, -4, 1, 4], [-2, -4, 2, 4], [-3, -4, 3, 4], [-3, -1, -4, 1, 4, 3]]

@[expose] def ruCSmallOrbit : List ℕ :=
  [710, 813, 1071, 1328, 1349, 1732, 1906, 2186, 2206, 2293, 2766, 2949]

@[expose] def ruCSmallPartition : List ℕ :=
  [0, 1, 0, 2, 3, 4, 3, 1, 2, 4, 5, 5]

@[expose] def ruNSmallOrbit : List ℕ :=
  [
    106, 168, 233, 349, 710, 813, 1071, 1179, 1328, 1349, 1732, 1906, 2058, 2186, 2206, 2293,
    2421, 2537, 2739, 2766, 2817, 2858, 2949, 3075, 3130, 3328, 3450, 4058]

@[expose] def ruNSmallPartition : List ℕ :=
  [
    0, 1, 2, 1, 3, 4, 3, 2, 5, 4, 3, 4, 6, 4, 5, 3, 0, 0, 1, 5, 6, 6, 5, 2, 2, 0, 1, 6]

@[expose] def ruDerivedProvenance : List (ℕ × ℕ × List ℤ) :=
  [(0, 2, []), (0, 3, []), (1, 3, []), (2, 3, []), (0, 3, [3])]

@[expose] def ruQuotientBits : List ℕ :=
  [1, 0, 2, 4]

@[expose] def ruCGenCount : ℕ :=
  2

@[expose] def ruCBase : List ℕ :=
  [0, 1, 2]

@[expose] def ruCDerivations : List (List ℤ) :=
  [
    [-2, -1, -1, 2, 2, 1, 1, 2], [-2, -1, -1, -2, -1, 2, 2, 1, 2, 1, 1],
    [3, 4, -2, -2, -1, -2, -2, -1, 2, 1, 1, 2, 2, 2],
    [-1, -1, -1, -1, -1, 2, 2, 1, 1, 1, 1, 1], [-1, -1, -1, -1, -2, -1, 2, 1, 2, 2, 2, 1, 1]]

@[expose] def ruNGenCount : ℕ :=
  2

@[expose] def ruNBase : List ℕ :=
  [0, 1, 2]

@[expose] def ruNDerivations : List (List ℤ) :=
  [
    [-2, -2, 1, 2, 2],
    [1, -2, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2],
    [-2, 1, -2, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
      2, 1, 2, 2, 1, 2, 2, 1, 2],
    [3, 5, 3, 5]]

@[expose] def ruJoinGenCount : ℕ :=
  4

@[expose] def ruJoinBase : List ℕ :=
  [0, 1, 2, 3]

@[expose] def ruJoinDerivations : List (List ℤ) :=
  [
    [-4, 3, 2, 1, 4], [-4, -4, 3, 4, 4], [-1, -2, -2, -2, 3, 2, 3, 1], [-1, 3, -1, 4, 3, 4, 1],
    [-8, -8, -8, 5, 8, 8, 8], [-8, -8, 6, -8, 6, 8, 8, 8], [5, -8, -8, 7, -8, 5, 8, 8, 8, 5],
    [5, -8, -8, -8, 6, 8, 8, 8, 5], [6, -8, -8, -8, 6, 8, 8, 7, 8, 6, 5],
    [5, -8, -8, 7, -8, -8, 7, 8, 8, 8, 8, 5], [11, -14, -13, 14, 9, 12],
    [-13, -14, -13, 14, 13, 12, 9], [9, 11, -13, -14, 9, -8, 5, -8, -8, -8, 6, 8, 8, 8, 5, 8],
    [11, -17, 12, -14, 5, -8, -8, -8, -8, -8, 7, 8, 8, 5, 8, 8, 5]]

@[expose] def ruCFaithfulGenCount : ℕ :=
  2

@[expose] def ruCFaithfulBase : List ℕ :=
  [0, 1]

@[expose] def ruCFaithfulDerivations : List (List ℤ) :=
  [
    [-2, -1, -1, 2, 2, 1, 1, 2], [-2, -1, -1, -2, -1, 2, 2, 1, 2, 1, 1],
    [-2, -2, -1, -2, -2, -1, 2, 1, 1, 2, 2, 2], [-1, -1, -1, -1, -1, 2, 2, 1, 1, 1, 1, 1],
    [-1, -1, -1, -1, -2, -1, 2, 1, 2, 2, 2, 1, 1]]

@[expose] def ruCQuotient80GenCount : ℕ :=
  2

@[expose] def ruCQuotient80Base : List ℕ :=
  [0, 1, 2, 4]

@[expose] def ruCQuotient80Derivations : List (List ℤ) :=
  [
    [-2, -2, -2, 1, 1, 1, 1], [-2, -1, -2, -1, 2, 2, 1, 2],
    [-1, -1, -2, -2, -1, 2, 1, 1, 2, 1], [-3, -4, 5, 3],
    [-3, -4, -4, -4, -1, -2, -2, -1, -2, 1, 2, 2, 2, 1],
    [-6, -6, -6, -5, -3, -7, -7, -1, -1, -2, -2, 1, 2, 1, 2, 2]]

@[expose] def ruSGenCount : ℕ :=
  4

@[expose] def ruSBase : List ℕ :=
  [1, 0]

@[expose] def ruSDerivations : List (List ℤ) :=
  [
    [3, -4, 1, 2, 4, 3], [1, -4, -4, 1, 2, 4, 4, 1], [1, -4, 1, 3, 4, 4, 4, 3]]

@[expose] def ruKGenCount : ℕ :=
  8

@[expose] def ruKBase : List ℕ :=
  [0, 1]

@[expose] def ruKDerivations : List (List ℤ) :=
  [
    [6, 4, 7, 4, 1], [4, 5, 2, 8, 1]]

@[expose] def ruJGenCount : ℕ :=
  6

@[expose] def ruJBase : List ℕ :=
  [0, 1]

@[expose] def ruJDerivations : List (List ℤ) :=
  [
    [2, 3, 2], [1, 3, 1, 3], [2, 1, 5, 4], [-5, 1, 5]]

@[expose] def ruRGenCount : ℕ :=
  5

@[expose] def ruRBase : List ℕ :=
  [0, 1]

@[expose] def ruRDerivations : List (List ℤ) :=
  [
    [1, 2, 2], [1, -2, 5, 2]]

@[expose] def ruS4060ChainBase : List ℕ :=
  [1, 0]

@[expose] def ruS4060ChainDerivations : List (List ℤ) :=
  [
    [-1, -3, -1, 4, 2, 1, 4, 1], [4, 4, -5, 3, 5, 4, 1]]

@[expose] def ruLChainBase : List ℕ :=
  [0, 2]

@[expose] def ruLChainDerivations : List (List ℤ) :=
  [
    [-1, -2, -1, -2, -1, -2, -3, 2, 3, 1, 3, 1, 2, 1], [-3, 4, -3, 2, 4, 3, 1],
    [-2, -5, -1, 2, -5, 3]]

@[expose] def ruMProg : List SlotRow :=
  [
    .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 5 7, .pwr 5 7 2, .pwr 11 5 6, .mu 3 6 7,
    .iv 7 6, .mu 6 2 3, .mu 3 7 2]

@[expose] def ruRMWord : List ℤ :=
  [
    2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]

@[expose] def ruAlignmentSeedWord : List ℤ :=
  [2, 1, 2]

@[expose] def ruAlignmentProductOrder : ℕ :=
  15

@[expose] def ruLMWords : List (List ℤ) :=
  [
    [1], [2, 2, 1, 2], [2, 1, 2, 2]]

@[expose] def ruSylowFusion : List (List ℤ × List ℤ × ℕ) :=
  [
    ([4, 3, 1], [2, 2, 1, 1], 7), ([4, 4, 2], [], 5), ([4, 4, 1, 3, 1, 4, 2, 1], [2, 2], 7)]

@[expose] def ruOddNormalObstructions : List (ℕ × List ℤ × ℕ) :=
  [
    (5, [2, 1, 2, 3, 2, 1, 3, 1, 2, 1], 3), (7, [1, 3, 1, 3, 2, 1, 2, 1], 3),
    (13, [1, 3, 2, 1, 2, 1, 3, 1], 3)]

end CFSG.Sporadic.RuSchreier
