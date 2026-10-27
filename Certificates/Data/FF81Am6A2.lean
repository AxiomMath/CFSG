module

public import Certificates.Data.RudvalisFF81Sp6RefS
public import Certificates.Data.FF81Am6LSide

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData

@[expose] def a2Z7 : List ℕ :=
  [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def a2Z7I : List ℕ :=
  [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0]

@[expose] def a2Tau0 : List ℕ :=
  [1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2Tau1 : List ℕ :=
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2Tau2 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2C0 : List ℕ :=
  [0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0,
    1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0]

@[expose] def a2C0I : List ℕ :=
  [0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1,
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1]

@[expose] def a2S0 : List ℕ :=
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1,
    1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1,
    0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]

@[expose] def a2C1 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1,
    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0]

@[expose] def a2C1I : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0,
    1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0,
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1]

@[expose] def a2S1 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1]

@[expose] def a2C2 : List ℕ :=
  [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0]

@[expose] def a2C2I : List ℕ :=
  [1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0]

@[expose] def a2S2 : List ℕ :=
  [0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0]

@[expose] def a2G0 : List ℕ :=
  [1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1,
    0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1,
    1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]

@[expose] def a2G0I : List ℕ :=
  [0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1,
    1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0,
    0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0]

@[expose] def a2G1 : List ℕ :=
  [1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1]

@[expose] def a2G1I : List ℕ :=
  [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0]

@[expose] def a2H : List ℕ :=
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
    1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1]

@[expose] def a2HI : List ℕ :=
  [1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0,
    1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1]

@[expose] def a2DA : List ℕ :=
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0,
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2DAI : List ℕ :=
  [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2DB : List ℕ :=
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0,
    1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1]

@[expose] def a2P : List ℕ :=
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0,
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2Q : List ℕ :=
  [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2EP : List ℕ :=
  [1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1,
    0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def a2EM : List ℕ :=
  [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]

@[expose] def a2GY : List ℕ :=
  [0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0,
    1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2GYI : List ℕ :=
  [1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0,
    0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2S01 : List ℕ :=
  [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2S10 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def a2S12 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1]

@[expose] def a2S21 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]

@[expose] def cj (g x gi : List ℕ) : List ℕ := mul6 (mul6 g x) gi

@[expose] def a2V : List ℕ := lsV

@[expose] def a2V2 : List ℕ := lsVInv

@[expose] def a2XGens (i : Fin 3) : List (List ℕ) :=
  ![[a2Z7, a2Tau0], [a2Z7, a2Tau1], [a2Z7, a2Tau2]] i

@[expose] def a2XTab (i : Fin 3) : Array (List ℕ) := closureT (a2XGens i)

@[expose] def a2K4Gens : List (List ℕ) := [a2V, lsSig]

@[expose] def a2K2Gens : List (List ℕ) := [a2P, a2Q]

@[expose] def a2DGens : List (List ℕ) := [a2DA, a2DB]

@[expose] def a2R : List ℕ := mul6 (mul6 a2P a2Q) a2P

@[expose] def capTab (gens : List (List ℕ)) : Array (List ℕ) :=
  build one6 mul6 gens (bfsParents one6 mul6 gens 168)

@[expose] def tabGe (n : ℕ) (tab : Array (List ℕ)) : Bool :=
  decide (n ≤ tab.size) && distinctCheck tab && allCheck canon6 tab

@[expose] def isThree (w : List ℕ) : Bool := !(w == one6) && mul6 (mul6 w w) w == one6

@[expose] def scanOne (m0 m1 m2 : Std.HashMap (List ℕ) ℕ) (τ : List ℕ) : Bool :=
  !isThree (mul6 a2Z7 τ) ||
    (let tab := capTab [a2Z7, τ]
     tabGe 168 tab && (tabGe 169 tab || found (a2XTab 0) m0 τ || found (a2XTab 1) m1 τ ||
       found (a2XTab 2) m2 τ))

@[expose] def scanCheck : Bool :=
  let m0 := indexMap (a2XTab 0)
  let m1 := indexMap (a2XTab 1)
  let m2 := indexMap (a2XTab 2)
  allCheck (scanOne m0 m1 m2) orbit0 && allCheck (scanOne m0 m1 m2) orbit1 &&
    allCheck (scanOne m0 m1 m2) orbit2 && allCheck (scanOne m0 m1 m2) orbit3

@[expose] def xCheck : Bool :=
  (List.finRange 3).all (fun i => closureOK (a2XGens i) (a2XTab i) 168) &&
    pairCheck (a2Z7, a2Z7I) && pairCheck (a2Tau0, a2Tau0) && pairCheck (a2Tau1, a2Tau1) &&
      pairCheck (a2Tau2, a2Tau2)

@[expose] def badOne (i : Fin 3) (c ci s g gi : List ℕ) : Bool :=
  pairCheck (c, ci) && pairCheck (s, s) && pairCheck (g, gi) && cj g c gi == a2V &&
    found (a2XTab i) (indexMap (a2XTab i)) c && found (a2XTab i) (indexMap (a2XTab i)) s &&
    closureOK [c, s] (closureT [c, s]) 6 &&
    countP (fun y => commutes6 y (cj g s gi)) (closureT ((centGens 4).map Prod.fst)) == 12

@[expose] def badCheck : Bool :=
  badOne 0 a2C0 a2C0I a2S0 a2G0 a2G0I && badOne 1 a2C1 a2C1I a2S1 a2G1 a2G1I

@[expose] def goodCheck : Bool :=
  pairCheck (a2C2, a2C2I) && pairCheck (a2S2, a2S2) && pairCheck (a2H, a2HI) &&
    found (a2XTab 2) (indexMap (a2XTab 2)) a2C2 && found (a2XTab 2) (indexMap (a2XTab 2)) a2S2 &&
    closureOK [a2C2, a2S2] (closureT [a2C2, a2S2]) 6 &&
    (cj a2H a2C2 a2HI == a2V || cj a2H a2C2 a2HI == a2V2) &&
    found (closureT a2K4Gens) (indexMap (closureT a2K4Gens)) (cj a2H a2S2 a2HI) &&
    closureOK a2K4Gens (closureT a2K4Gens) 6

@[expose] def cenListed (a : List ℕ) : Bool :=
  a == vecCode 1 1 0 || a == vecCode 2 2 0 || a == vecCode 0 0 1 || a == vecCode 0 0 2 ||
    a == vecCode 1 1 1 || a == vecCode 2 2 2 || a == vecCode 1 1 2 || a == vecCode 2 2 1

@[expose] def cenCount (a t : List ℕ) : ℕ :=
  if a == vecCode 1 1 0 || a == vecCode 2 2 0 then
    countP (fun y => commutes6 y t) (closureT ((centGens 3).map Prod.fst))
  else if a == vecCode 0 0 1 || a == vecCode 0 0 2 then
    countP (fun y => commutes6 y t) (closureT ((centGens 2).map Prod.fst))
  else if a == vecCode 1 1 1 || a == vecCode 2 2 2 then
    countP (fun y => commutes6 y t) (closureT (c7P.map Prod.fst))
  else if a == vecCode 1 1 2 || a == vecCode 2 2 1 then
    countP (fun y => commutes6 y (cj fl2C t fl2C)) (closureT (c7P.map Prod.fst))
  else 0

@[expose] def dPair (m2 : Std.HashMap (List ℕ) ℕ) (a t : List ℕ) : Bool :=
  !(mul6 (mul6 a a) a == one6 && !(a == one6) && mul6 t t == one6 && !(t == one6) &&
      mul6 (mul6 t a) t == mul6 a a) ||
    (found (closureT a2K2Gens) m2 a && found (closureT a2K2Gens) m2 t) ||
    (cenListed a && cenCount a t != 36)

@[expose] def dGroup : Bool :=
  closureOK a2DGens (closureT a2DGens) 36 &&
    pairCheck (a2DA, a2DAI) && pairCheck (a2DB, a2DB) &&
    commutes6 a2DA a2V && commutes6 a2DA lsSig && commutes6 a2DB a2V && commutes6 a2DB lsSig

@[expose] def dClass : Bool :=
  allCheck (fun a => allCheck (dPair (indexMap (closureT a2K2Gens)) a) (closureT a2DGens))
    (closureT a2DGens)

@[expose] def dCheck : Bool := dGroup && dClass

@[expose] def chainPairs : Bool :=
  pairCheck (a2GY, a2GYI) && pairCheck (a2P, a2P) && pairCheck (a2Q, a2Q) &&
    pairCheck (a2EP, a2EP) && pairCheck (a2EM, a2EM)

@[expose] def chainXstar : Bool :=
  found (a2XTab 2) (indexMap (a2XTab 2)) (cj a2HI a2EP a2H) &&
    found (a2XTab 2) (indexMap (a2XTab 2)) (cj a2HI a2EM a2H)

@[expose] def chainK2 : Bool :=
  closureOK a2K2Gens (closureT a2K2Gens) 6 &&
    allCheck (fun t => !(mul6 t t == one6) || t == one6 || t == a2P || t == a2Q || t == a2R)
      (closureT a2K2Gens)

@[expose] def chainSiegel : Bool :=
  cj a2GY a2S01 a2GYI == a2P && cj a2GY a2S10 a2GYI == a2Q &&
    cj a2GY a2S12 a2GYI == a2EP && cj a2GY a2S21 a2GYI == a2EM &&
    cj j6C a2S01 j6C == a2S10 && cj j6C a2S10 j6C == a2S01 &&
    cj j6C a2S12 j6C == a2S21 && cj j6C a2S21 j6C == a2S12

@[expose] def chainWords : Bool :=
  mul6 (mul6 (mul6 (cj a2R a2EP a2R) a2EM) (cj a2R a2EP a2R)) a2EM == a2P &&
    mul6 (mul6 (mul6 a2EP (cj a2R a2EM a2R)) a2EP) (cj a2R a2EM a2R) == a2Q

@[expose] def chainCheck : Bool :=
  chainPairs && chainXstar && chainK2 && chainSiegel && chainWords

@[expose] def a2Check : Bool :=
  xCheck && scanCheck && badCheck && goodCheck && dCheck && chainCheck

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
