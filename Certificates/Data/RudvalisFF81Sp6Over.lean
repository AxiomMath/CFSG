module

public import Certificates.Data.RudvalisFF81Sp6Transv
public import CFSG.Quasithin.H13.L32NMatNInputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.Quasithin.H13.MatNCert

@[expose] def ovGamC : List ℕ :=
  [0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 0]

@[expose] def ovGamI : List ℕ :=
  [0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0,
    1, 0, 0, 1, 0]

@[expose] def ovHC : List ℕ :=
  [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0,
    1, 0, 1, 0, 1]

@[expose] def ovHI : List ℕ :=
  [0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1,
    1, 0, 0, 1, 0]

@[expose] def ovCC : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1,
    1, 0, 0, 0, 0]

@[expose] def ovCI : List ℕ :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0,
    0, 0, 1, 0, 1]

@[expose] def genC : List (List ℕ) := [ovGamC, ovHC, ovCC]

@[expose] def wordC (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mul6 (genC.getD i one6) acc) one6

@[expose] def wZ0 : List ℕ := [0, 2, 0, 0, 2, 1, 2, 0, 0, 0, 2, 0, 0, 0]

@[expose] def wZ1 : List ℕ := [2, 2, 0, 0, 1, 0, 2, 0, 2, 2, 1, 0, 1]

@[expose] def wT : List ℕ := [0, 0, 2, 2, 2, 0, 0, 2, 1, 2, 1, 0, 1, 2, 1]

@[expose] def wS : List (List ℕ) :=
  [[2, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 2, 1, 2], [1, 1, 1, 2, 0, 0, 2, 0, 2, 1, 2, 2, 2, 0],
    [1, 1, 2, 1, 0, 1, 2, 1, 0, 0, 2, 0, 2, 2, 0], [0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1],
    [1, 1, 2, 1, 2, 2, 0, 1, 2, 1, 0, 0, 2, 0, 0]]

@[expose] def wP1 : List ℕ := [0, 1, 2, 2, 0, 0, 1, 2, 2, 1, 0, 1, 2, 2]

@[expose] def relW : List (List ℕ × ℕ) :=
  [([2], 6), ([0, 2], 7), ([1, 2], 6), ([0, 1, 2], 5), ([0, 0, 2], 7), ([0, 2, 2], 4),
    ([1, 2, 2], 2), ([0, 2, 0, 2, 2, 2, 2, 2], 7), ([1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2], 3),
    ([0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2], 6), ([0, 1, 2, 2], 6), ([0, 0, 0, 2], 6),
    ([2, 0, 2, 0, 0, 0, 0, 0, 0], 6)]

@[expose] def h6Chk899108 : Bool :=
  pairCheck (ovGamC, ovGamI) && pairCheck (ovHC, ovHI) && pairCheck (ovCC, ovCI) &&
    relW.all (fun r => powCode (wordC r.1) r.2 == one6) &&
    powCode ovGamC 7 == one6 && !(ovGamC == one6) && powCode ovHC 6 == one6 &&
    mul6 ovHC ovGamC == mul6 (powCode ovGamC 3) ovHC &&
    mul6 ovCC (mul6 ovHC ovHC) == mul6 (mul6 ovHC ovHC) ovCC &&
    wordC wZ0 == zCode 0 && wordC wZ1 == zCode 1 && wordC wT == tCode &&
    wS.map wordC == sylowP.map Prod.fst &&
    powCode (wordC [0, 1, 2]) 5 == one6 && !(wordC [0, 1, 2] == one6)

@[expose] def nGc : List ℕ := [1, 4, 8, 6, 32, 64, 80]

@[expose] def nHc : List ℕ := [1, 16, 80, 96, 2, 6, 10]

@[expose] def xSc : List ℕ := [1, 18, 92, 100, 16, 20, 24]

@[expose] def xIc : List ℕ := [1, 19, 92, 100, 16, 20, 24]

@[expose] def n2c : List ℕ := mulN nHc nHc

@[expose] def fixL : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19]

@[expose] def wL : List ℕ := [0, 4, 8, 12, 48, 52, 56, 60, 80, 84, 88, 92, 96, 100, 104, 108]

@[expose] def cand (a u b v : ℕ) : List ℕ := [1, a, u, mvN n2c u, b, v ^^^ b, mvN n2c v ^^^ b]

@[expose] def relsOK (x : List ℕ) : Bool :=
  relW.all fun r => powN 7 (evalW 7 [nGc, nHc, x] r.1) r.2 == oneN 7

@[expose] def pinChk899108 : Bool :=
  (List.range 128).all (fun c => !(mvN n2c c == c) || fixL.contains c) &&
    (List.range 128).all (fun c => !(mvN n2c (mvN n2c c) == (c ^^^ mvN n2c c)) || wL.contains c) &&
    fixL.all fun a => wL.all fun u => fixL.all fun b => wL.all fun v =>
      !relsOK (cand a u b v) || cand a u b v == xSc || cand a u b v == xIc

@[expose] def kC (m : ℕ) : List ℕ := 1 :: (List.range 6).map fun j => 2 ^ (j + 1) + m / 2 ^ j % 2

@[expose] def conj7 (y gp : List ℕ) : List ℕ := mulN (mulN (gp.take 7) y) (gp.drop 7)

@[expose] def orbR (act : List ℕ → List ℕ → List ℕ) (dflt t : List ℕ) (gens : List (List ℕ))
    (par : List (ℕ × ℕ)) : Array (List ℕ) :=
  par.foldl (fun acc ps => acc.push (act (acc.getD ps.1 t) (gens.getD ps.2 dflt))) #[t]

@[expose] def kGps (x : List ℕ) : List (List ℕ) :=
  [nGc ++ powN 7 nGc 6, nHc ++ powN 7 nHc 5, x ++ powN 7 x 5]

@[expose] def kTab (x : List ℕ) : Array (List ℕ) :=
  orbR conj7 (oneN 7 ++ oneN 7) (kC 1) (kGps x) (bfsParents (kC 1) conj7 (kGps x) 64)

@[expose] def bbarC (x : List ℕ) : List ℕ := evalW 7 [nGc, nHc, x] wZ1

@[expose] def rGens (x : List ℕ) : List (List ℕ) :=
  [kC 6, kC 8, kC 17, kC 33, evalW 7 [nGc, nHc, x] wP1]

@[expose] def caseChk (x : List ℕ) : Bool :=
  (kGps x).all (fun gp => mulN (gp.take 7) (gp.drop 7) == oneN 7 &&
      mulN (gp.drop 7) (gp.take 7) == oneN 7) &&
    (let tab := kTab x
     (List.range 64).all fun m => m == 0 || found tab (indexMap tab) (kC m)) &&
    ((List.range 128).filter fun v => mvN (bbarC x) v == v).length == 32 &&
    (rGens x).all (fun g => mulN g (bbarC x) == mulN (bbarC x) g) &&
    [6, 8, 17, 33].all (fun m => mulN (kC m) (kC m) == oneN 7) &&
    subB 7 (rGens x) (elemsOf 7 (rGens x) 64) && (elemsOf 7 (rGens x) 64).length == 32

@[expose] def kChk899108 : Bool :=
  caseChk xSc && caseChk xIc

@[expose] def piC (x : List ℕ) : List ℕ := (x.drop 1).map (· / 2)

@[expose] def sbGens : List (List ℕ) := [piC nGc, piC nHc, piC xSc]

@[expose] def pibbarC : List ℕ := evalW 6 sbGens wZ1

@[expose] def uGens : List (List ℕ) :=
  [[1, 15, 9, 5, 29, 45], [1, 39, 33, 45, 53, 5], [2, 1, 7, 8, 30, 45]]

@[expose] def uChk899108 : Bool :=
  piC xIc == piC xSc &&
    uGens.all (fun u => mulN u u == oneN 6 && mulN u pibbarC == mulN pibbarC u) &&
    subB 6 uGens (elemsOf 6 uGens 64) && (elemsOf 6 uGens 64).length == 32

@[expose] def bitsOf (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bitsOf f k ^^^ (if f k then 2 ^ k else 0)

@[expose] def formAct (w g : List ℕ) : List ℕ :=
  (List.range 6).map fun j => bitsOf (fun i => dotN 6 (g.getD i 0) (mvN w (g.getD j 0))) 6

@[expose] def w0c : List ℕ := [56, 48, 32, 1, 3, 7]

@[expose] def sbInv : List (List ℕ) :=
  [powN 6 (piC nGc) 6, powN 6 (piC nHc) 5, powN 6 (piC xSc) 5]

@[expose] def grs : List (List ℕ) :=
  [[17, 25, 58, 13, 56, 29], [53, 21, 18, 33, 8, 42], [37, 60, 51, 18, 14, 48],
    [19, 7, 53, 37, 18, 58], [32, 45, 3, 59, 31, 6]]

@[expose] def grsInv : List (List ℕ) :=
  [[41, 20, 34, 3, 40, 59], [11, 51, 62, 16, 55, 3], [22, 50, 13, 47, 58, 26],
    [17, 28, 15, 38, 12, 22], [61, 57, 25, 39, 42, 1]]

@[expose] def fTab (w : List ℕ) (gens : List (List ℕ)) : Array (List ℕ) :=
  orbR formAct (oneN 6) w gens (bfsParents w formAct gens 14000)

@[expose] def fAll : Array (List ℕ) :=
  grs.foldl (fun acc g => acc ++ fTab (formAct w0c g) sbGens) #[w0c]

@[expose] def formChk899108 : Bool :=
  validB 6 w0c && sbGens.all (validB 6) && grs.all (validB 6) &&
    sbGens.all (fun g => formAct w0c g == w0c) &&
    sbGens.all (fun g => sbInv.any fun h => validB 6 h && mulN g h == oneN 6 &&
      mulN h g == oneN 6) &&
    grs.all (fun g => grsInv.any fun h => validB 6 h && mulN g h == oneN 6 &&
      mulN h g == oneN 6) &&
    grs.all (fun g => let t := fTab w0c (sbGens ++ [g])
      t.size == 13888 && distinctCheck t && allCheck (validB 6) t) &&
    fAll.size == 13888 && distinctCheck fAll && allCheck (validB 6) fAll

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
