
module

public import CFSG.Sporadic.Co1.Module.OddProg

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix

def code4 : ℕ := 10075731

def brayIdx : List ℕ := [31, 35, 39, 43, 47, 51, 55, 59]

def brayInvIdx : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67]

def sIdx : List ℕ := [70, 73, 76]

def pvIdx : List ℕ := [68, 71, 74]

def zIdx : List (List ℕ) := [[77, 78, 79, 80], [81, 82], [83, 84]]

def Mt (i : ℕ) : Array ℕ := transposeRows 24 (rr i)

def isT4 (x : ℕ) : Bool :=
  type4N (transposeRows 24 qRows) (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x

def validOK : Bool :=
  (List.range 94).all (fun i => validRows (rr i)) && validRows (idRows 24) &&
  (mulRows 24 (rr 23) (rr 24) == idRows 24) && (mulRows 24 (rr 17) (rr 25) == idRows 24) &&
  (List.range 8).all (fun i => mulRows 24 (rr (brayIdx[i]!)) (rr (brayInvIdx[i]!)) == idRows 24) &&
  isT4 code4

def fixOK : Bool :=
  ([23, 17, 27, 86] ++ brayIdx ++ sIdx ++ zIdx.flatten).all (fun i => isFixedN (Mt i) code4) &&
  (mulRows 24 (rr 27) (rr 27) == idRows 24) && (mulRows 24 (rr 86) (rr 86) == idRows 24) &&
  brayIdx.all (fun i => mulRows 24 (rr i) (rr 27) == mulRows 24 (rr 27) (rr i))

def partnerOK : Bool :=
  (List.range 3).all (fun k =>
    (zIdx[k]!).all (fun z =>
      (mulRows 24 (rr z) (rr 27) == mulRows 24 (rr 27) (rr z)) &&
      (mulRows 24 (rr z) (rr (sIdx[k]!)) == mulRows 24 (rr (sIdx[k]!)) (rr z))) &&
    (mulRows 24 (rr (pvIdx[k]!)) (rr (pvIdx[k]! + 1)) == idRows 24) &&
    (rr (sIdx[k]!) == mulRows 24 (mulRows 24 (rr (pvIdx[k]!)) (rr 27)) (rr (pvIdx[k]! + 1))))

def conjOK : Bool :=
  (mulRows 24 (rr 91) (rr 27) == mulRows 24 (rr 89) (rr 91)) &&
  (mulRows 24 (rr 93) (rr 89) == mulRows 24 (rr 86) (rr 93)) &&
  (orderN (mulRows 24 (rr 27) (rr 70)) == 3) && (orderN (mulRows 24 (rr 27) (rr 73)) == 3) &&
  (orderN (mulRows 24 (rr 27) (rr 76)) == 5)

def fixOK₂ : Bool :=
  (fixCount [Mt 27] == 65536) &&
  (fixCount4 [Mt 27] (transposeRows 24 qRows) (orbitOf 2 98280).pts
    (posTable 24 (orbitOf 2 98280).pts) 98280 == 32535)

def pairFixOK (k fx f4 : ℕ) : Bool :=
  (fixCount [Mt 27, Mt (sIdx[k]!)] == fx) &&
  (fixCount4 [Mt 27, Mt (sIdx[k]!)] (transposeRows 24 qRows) (orbitOf 2 98280).pts
    (posTable 24 (orbitOf 2 98280).pts) 98280 == f4)

def PS : Array (Array ℕ) := #[rr 23, rr 17]

def QS : Array (Array ℕ) := #[rr 24, rr 25]

def rootsS : Array (Array ℕ) := #[rr 86, rr 27]

def FS : Forest := forestBFS PS QS rootsS 10000000

def ordsR : Array ℕ := ordersWith (rr 27) FS

def ords1 : Array ℕ := ordersWith (rr 86) FS

def forestSOK : Bool :=
  forestOK PS QS rootsS FS && (FS.pts.size == 182919) && (rtCount FS 0 == 759) &&
  (rtCount FS 1 == 182160) && (zeroCount ordsR == 0) && (oddCount ordsR == 37888) &&
  (zeroCount ords1 == 0) && (oddCount ords1 == 0)

def PO : Array (Array ℕ) := (brayIdx.map rr).toArray

def QO : Array (Array ℕ) := (brayInvIdx.map rr).toArray

def rootsO : Array (Array ℕ) := (sIdx.map rr).toArray

def FO : Forest := forestBFS PO QO rootsO 10000000

def forestOOK : Bool :=
  forestOK PO QO rootsO FO && (FO.pts.size == 37888) && (rtCount FO 0 == 7168) &&
  (rtCount FO 1 == 2048) && (rtCount FO 2 == 28672)

def QZ (k : ℕ) : Array (Array ℕ) := ((zIdx[k]!).map rr).toArray

def PZ (k : ℕ) : Array (Array ℕ) := ((zIdx[k]!).map fun _ => idRows 24).toArray

def rootsZ : Array (Array ℕ) := #[idRows 24]

def FZ (k : ℕ) : Forest := forestBFS (PZ k) (QZ k) rootsZ 10000000

def forestZOK (k n : ℕ) : Bool :=
  forestOK (PZ k) (QZ k) rootsZ (FZ k) && ((FZ k).pts.size == n)

def Wk (k : ℕ) : List ℕ := fixList ([rr 27, rr (sIdx[k]!)].map (transposeRows 24))

def faithGramOK (k : ℕ) : Bool :=
  faithfulOK (FZ k).pts (Wk k) && gramOK (transposeRows 24 f0Rows) (Wk k)

end CFSG.Sporadic.Co1.Module.Odd
