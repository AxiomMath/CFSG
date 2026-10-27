module

public import CFSG.Monster.B.TwoA.Fischer.CertSieve
public meta import CFSG.Monster.B.TwoA.Fischer.CertSieve

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

@[expose] def fourGen (k : ℕ) : ℕ := [0, 1, 2, 12][k]!

@[expose] def seedWord : List ℕ := [3, 2, 0, 2, 3, 1, 2, 0, 2, 3]

@[expose] def seedPre : ℕ := seedWord.foldr (fun k acc => vecMulN 78 (fourColArr[k]!) acc) 949

@[expose] def rootOpNum (z x : ℕ) : ℕ :=
  x ^^^ vecMulN 78 (adCols z) x ^^^
    if dotBit 78 z (vecMulN 78 (transposeRows 78 gramRowArr) x) then z else 0

@[expose] def seedLabels : List ℕ :=
  [22, 36, 42, 48, 119, 130, 139, 142, 184, 197, 204, 209, 217, 227, 237, 239, 353, 354, 366,
    373, 382, 402, 414, 421, 433, 434, 449, 469, 573, 575, 585, 595, 604, 609, 616, 629, 667,
    670, 679, 690, 762, 768, 774, 788, 869, 881, 897, 898, 910, 917, 930, 942, 958, 965, 977,
    978, 1049, 1051, 1064, 1066, 1078, 1081, 1083, 1084, 1398, 1407, 1421, 1428, 1439, 1445,
    1454, 1460, 1468, 1477, 1480, 1489, 1496, 1498, 1657, 1663, 1672, 1678, 1750, 1756, 1768,
    1770, 1817, 1829, 1832, 1844, 2006, 2021, 2029, 2030, 2075, 2082, 2087, 2094, 2199, 2212,
    2423, 2433, 2438, 2448, 2488, 2490, 2505, 2507, 2678, 2687, 2715, 2728, 2939, 2946, 2951,
    2958, 3008, 3013, 3016, 3021, 3140, 3157, 3319, 3346, 3387, 3400]

@[expose] def fourCheck : Bool :=
  fourColArr.size == 4 && fourColArr.all (·.size == 78) &&
    (List.range 4).all fun k => (List.range 78).all fun i =>
      (fourColArr[k]!)[i]! == labelCoord ((indCandidate (fourGen k))[basisPt i]!)

@[expose] def seedZeroCheck : Bool :=
  let a := adCols 16058837527637121392057
  (List.range 3510).all fun q =>
    let b := vecMulN 78 a (labelCoord q)
    decide (b < 2 ^ 78) && (b == 0) == seedLabels.contains q

end CFSG.Monster.B.TwoA.Fischer.Cert
