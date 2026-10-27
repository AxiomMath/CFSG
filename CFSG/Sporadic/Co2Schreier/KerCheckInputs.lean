
module

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert

structure KerData where
  d : Array (Array ℕ)
  zs : Array (Array ℕ)
  r : Array (Array ℕ)
  z : Array ℕ
  derivD : List (List ℤ)
  derivLegacy : List (List ℤ)
  rWords : List (List ℤ)
  fixedIdx : List ℕ
  addWords : List (List ℤ)
  survivors : List (List ℕ)
  lv : Array Level
  base : Array ℕ

@[expose] def candArrs (K : KerData) (k0 k1 : ℕ) : Array (Array ℕ) :=
  #[compA 2300 K.d[0]! K.zs[k0]!, compA 2300 K.d[1]! K.zs[k1]!]

@[expose] def candOK (K : KerData) (k0 k1 : ℕ) : Bool :=
  K.fixedIdx.all (fun j => eqA 2300 (extendArrs (candArrs K k0 k1) K.derivD)[j]!
      (extendArrs K.d K.derivD)[j]!) &&
    allLt K.rWords.length (fun i => eqA 2300
      (wordArr (extendArrs (candArrs K k0 k1) K.derivLegacy) (K.rWords.getD i [])) K.r[i]!) &&
    K.addWords.all (fun w => eqA 2300 (wordArr (candArrs K k0 k1) w) (wordArr K.d w))

@[noinline, expose] def kerCheck (K : KerData) : Bool :=
  K.zs.size == 32 && K.d.size == 2 && K.r.size == K.rWords.length &&
    K.survivors == [[0, 0], [0, 9]] &&
    allLt 32 (fun k0 => allLt 32 fun k1 => !candOK K k0 k1 || K.survivors.contains [k0, k1]) &&
    allLt 32 (fun k0 => allLt 32 fun k1 =>
      allInv (extendArrs (candArrs K k0 k1) K.derivD) &&
        allInv (extendArrs (candArrs K k0 k1) K.derivLegacy)) &&
    allInv (extendArrs K.d K.derivD) &&
    extWordsOK 2 K.derivD && extWordsOK 2 K.derivLegacy &&
    K.rWords.all (lettersOK (2 + K.derivLegacy.length)) &&
    K.addWords.all (lettersOK 2) &&
    K.fixedIdx.all (fun j => decide (j < 2 + K.derivD.length) &&
      siftA 2300 K.lv K.base 0 (extendArrs K.d K.derivD)[j]!) &&
    K.addWords.all (fun w => siftA 2300 K.lv K.base 0 (wordArr K.d w)) &&
    eqA 2300 K.zs[0]! (idA 2300) && commA K.d[0]! K.z && !commA K.d[1]! K.z &&
    eqA 2300 (compA 2300 K.z K.d[1]!) (compA 2300 (compA 2300 K.d[1]! K.zs[9]!) K.z)

@[expose] def kerData : KerData where
  d := dArrs
  zs := (centerIdxR.map fun k => enumR.elems[k]!).toArray
  r := rArrs
  z := zArr
  derivD := localRec.chains.D.derivations
  derivLegacy := localRec.dStrongDerivations
  rWords := localRec.rWords
  fixedIdx := witRec.wLocal.dStrongFixedBySIndices
  addWords := witRec.wLocal.dAdditionalFixedWords
  survivors := witRec.wLocal.dCandidateSurvivors
  lv := levelsS
  base := localRec.chains.S.baseArr

end CFSG.Sporadic.Co2Schreier
