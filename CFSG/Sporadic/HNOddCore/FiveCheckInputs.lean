module

public import CFSG.Sporadic.HNOddCore.XCheck
public import CFSG.Sporadic.HNOddCore.SCheck
public import CFSG.Sporadic.HNOddCore.FiveData
public import CFSG.Sporadic.HNSchreier.FALocalCheck
public meta import CFSG.Sporadic.HNOddCore.XCheck
public meta import CFSG.Sporadic.HNOddCore.SCheck
public meta import CFSG.Sporadic.HNOddCore.FiveData
public meta import CFSG.Sporadic.HNSchreier.FALocalCheck

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native CFSG.Certificates.Native

@[expose] def natBase5 : List (Fin 12) := [5, 6, 7, 8, 9]

@[expose] def evalPos (T : Array (Array Nat)) : List Int → Nat → Nat
  | [], x => x
  | l :: w, x => (T[l.toNat - 1]!)[evalPos T w x]!

@[expose] def labPos : Array Nat := (FAData.nbrLabels.map Prod.fst).toArray

@[expose] def labLet : Array Nat := (FAData.nbrLabels.map Prod.snd).toArray

@[expose] def gammaOK (O7 O42 : Array Nat) : Bool :=
  FAData.gamma.size == 50 &&
    (allBelowN 50 fun i => (FAData.gamma[i]!).length == 7 && (FAData.gamma[i]!).Nodup &&
      (FAData.gamma[i]!).all (fun j =>
        decide (j < 50) && j != i && (FAData.gamma[j]!).contains i)) &&
    (allBelowN 50 fun i => !O42.contains i ||
      ((FAData.gamma[i]!).countP fun j => O7.contains j) == 1) &&
    (allBelowN 50 fun j => !O7.contains j ||
      ((List.range 50).countP fun i => O42.contains i && (FAData.gamma[i]!).contains j) == 6)

@[expose] def natImgs (nS : Array (Array Nat)) (W : Array (List Int)) : Array (Array Nat) :=
  W.map (pword 12 nS (pinvs 12 nS))

@[expose] def iSm : Array (Array Nat) := FAData.iSmall.map List.toArray

@[expose] def aSm : Array (Array Nat) := FAData.aSmall.map List.toArray

@[expose] def a6Sm : Array (Array Nat) := FAData.a6Small.map List.toArray

@[expose] def orb7 : Array Nat := bfsList 50 aSm 17

@[expose] def orb42 : Array Nat := bfsList 50 aSm 1

@[expose] def orb1 : Array Nat := bfsList 50 aSm 0

@[expose] def orbI : Array Nat := bfsList 50 iSm 0

@[expose] def natChainOK (nS : Array (Array Nat)) : Bool :=
  (natImgs nS FAData.aWords).size == 5 &&
    chainCheck 12 (natImgs nS FAData.aWords) FiveData.natWords natBase5 FiveData.natSizes

@[expose] def a6NatOK (nS : Array (Array Nat)) : Bool :=
  FAData.a6Words.size == 4 &&
    allBelowN 4 fun k => plettersOK 17 FAData.a6Words[k]! &&
      allBelowN 6 fun i => ((natImgs nS FAData.a6Words)[k]!)[i]! == i

@[expose] def iOrbitOK : Bool :=
  iSm.size == 6 && (allBelowN 6 fun k => (iSm[k]!).size == 50) && orbitOK 50 iSm orbI &&
    orbI.size == 50

@[expose] def aOrbitsOK : Bool :=
  aSm.size == 5 && (allBelowN 5 fun k => aSm[k]! == iSm[k]!) &&
    orbitOK 50 aSm orb1 && orb1.size == 1 && orb1[0]! == 0 &&
    orbitOK 50 aSm orb7 && orb7.size == 7 && orb7[0]! == 17 &&
    orbitOK 50 aSm orb42 && orb42.size == 42 && orb42[0]! == 1 &&
    allBelowN 50 fun i => orb1.contains i || orb7.contains i || orb42.contains i

@[expose] def labelsOK (nS : Array (Array Nat)) : Bool :=
  labPos.size == 7 && labPos.toList.Nodup && (allBelowN 7 fun i => orb7.contains labPos[i]!) &&
    labLet == #[5, 6, 7, 8, 9, 10, 11] &&
    allBelowN 5 fun k => allBelowN 7 fun i =>
      labPos.contains (aSm[k]!)[labPos[i]!]! &&
        labLet[labPos.idxOf (aSm[k]!)[labPos[i]!]!]! ==
          ((natImgs nS FAData.aWords)[k]!)[labLet[i]!]!

@[expose] def fiberOK : Bool :=
  a6Sm.size == 4 && (allBelowN 4 fun k => (a6Sm[k]!).size == 50 && (a6Sm[k]!)[17]! == 17 &&
    FAData.fiber.all fun x => FAData.fiber.contains (a6Sm[k]!)[x]!) &&
    FAData.fiber == ((List.range 50).filter fun i => orb42.contains i &&
      (FAData.gamma[i]!).contains 17)

@[expose] def pairsOK : Bool :=
  FiveData.pairWords.size == 30 && FiveData.fiberPairs.length == 30 &&
    (allBelowN 30 fun p => (FiveData.pairWords[p]!).all (fun l => decide (0 < l ∧ l ≤ 4)) &&
      (evalPos a6Sm FiveData.pairWords[p]! 10, evalPos a6Sm FiveData.pairWords[p]! 13) ==
        FiveData.fiberPairs[p]!) &&
    FiveData.fiberPairs == (FAData.fiber.flatMap fun x =>
      (FAData.fiber.filter (· != x)).map fun y => (x, y))

@[noinline, expose] def fiveSmallChecksN (nS : Array (Array Nat)) : Bool :=
  natChainOK nS && a6NatOK nS && iOrbitOK && aOrbitsOK && labelsOK nS && gammaOK orb7 orb42 &&
    fiberOK && pairsOK

@[noinline, expose] def fiveSmallChecks : Bool :=
  fiveSmallChecksN
    (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords)

end CFSG.Sporadic.HNOddCore.Native
