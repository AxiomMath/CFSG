module

public import CFSG.Sporadic.SuzOddCore.GammaCheck
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.GammaCheck
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

@[expose] def fullExtArrList : Nat → Array (Array Nat)
  | 0 => (localStrongIdx.map fun j => certStrongArrs[j]!).toArray
  | k + 1 =>
    let L := fullExtArrList k
    L.push (wordA 22880 L (L.map (invCand 22880)) (localDerivs.getD (8 + k) []))

@[expose] def fullExtArrs : Array (Array Nat) := fullExtArrList 6

@[expose] def tFullOf (F : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 5) fun i => wordA 22880 F (F.map (invCand 22880)) (sylowQuotWords.getD i [])

@[expose] def tCompOf (T : Array (Array Nat)) : Array (Array Nat) := T.map (restrictArr localDomain)

@[expose] def compactEnum (T : Array (Array Nat)) : Enum := enumBFS 280 (tCompOf T) 729

@[expose] def fusionTransArr : Array Nat :=
  wordA 22880 #[certArr 0, certArr 1] #[invCand 22880 (certArr 0), invCand 22880 (certArr 1)]
    [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2]

@[expose] def normWordArr (k : Nat) : Array Nat :=
  wordA 280 localGenArrs (localGenArrs.map (invCand 280)) (normWords.getD k [])

@[expose] def normConj (k : Nat) : Array Nat :=
  compA 280 (normWordArr k) (compA 280 (centerCompact 3) (invCand 280 (normWordArr k)))

@[expose] def zChecks : Bool :=
  let z := zArr
  let z2 := compA 22880 z z
  eqA 22880 (compA 22880 z z2) (idA 22880) && !(eqA 22880 z (idA 22880)) && z[0]! == 0 &&
    certStabIdx.all (fun j =>
      let c := compA 22880 certStrongArrs[j]! (compA 22880 z certStrongInvs[j]!)
      eqA 22880 c z || eqA 22880 c z2) &&
    deltaOf z == localDomain

@[expose] def localChecks (F : Array (Array Nat)) : Bool :=
  F.size == 14 && localDomain.length == 280 &&
    (allLt 8 fun k =>
      restrictArr localDomain certStrongArrs[localStrongIdx.getD k 0]! == localGenArrs[k]!) &&
    (allLt 14 fun j => isInvA 22880 F[j]! (invCand 22880 F[j]!) &&
      restrictArr localDomain F[j]! == localStrongArrs[j]!) &&
    rawChainOK 280 localGenArrs localStrongArrs localBaseNat.toArray localDerivs 4 &&
    (rawOrbitSizes 280 localStrongArrs localBaseNat.toArray).prod == 6531840 &&
    (rawOrbitSizes 280 localStrongArrs localBaseNat.toArray).head? == some 280

@[expose] def sylowCenterChecks (T : Array (Array Nat)) (E : Enum) : Bool :=
  let z := zArr
  let C := tCompOf T
  let c := centerFull 3
  let cc := centerCompact 3
  enumOK 280 C E && E.tabs.size == 729 &&
    (allLt E.tabs.size fun k =>
      !(allLt 5 fun a => comp 280 C[a]! E.tabs[k]! == comp 280 E.tabs[k]! C[a]!) ||
        E.tabs[k]! == idTab 280 || E.tabs[k]! == cc || E.tabs[k]! == comp 280 cc cc) &&
    (allLt 9 fun r =>
      permOK 22880 (centerFull r) &&
        eqA 22880 (centerFull r)
          (compA 22880 (powArr 22880 c (r / 3)) (powArr 22880 z (r % 3)))) &&
    (allLt 9 fun r => allLt 9 fun r' => !(decide (r < r')) ||
      !(eqA 22880 (centerFull r) (centerFull r'))) &&
    eqA 22880 (compA 22880 (centerFull 1) (centerFull 1)) (centerFull 2) &&
    eqA 22880 (compA 22880 (centerFull 3) (centerFull 3)) (centerFull 6) &&
    eqA 22880 (compA 22880 (centerFull 4) (centerFull 4)) (centerFull 8) &&
    eqA 22880 (compA 22880 (centerFull 5) (centerFull 5)) (centerFull 7) &&
    eqA 22880 c T[1]! && restrictArr localDomain c == cc && !(cc == idTab 280) &&
    eqA 22880 (compA 22880 c z) (compA 22880 z c) &&
    (allLt 5 fun a => eqA 22880 (compA 22880 c T[a]!) (compA 22880 T[a]! c) &&
      eqA 22880 (compA 22880 z T[a]!) (compA 22880 T[a]! z)) &&
    eqA 22880 (powArr 22880 c 3) (idA 22880)

@[expose] def fusionNormChecks : Bool :=
  let g := fusionTransArr
  isInvA 22880 g (invCand 22880 g) &&
    eqA 22880 (compA 22880 g (compA 22880 zArr (invCand 22880 g))) (centerFull 5) &&
    g[0]! == 95 && fixedCountN 22880 (centerFull 3) == 38 &&
    fixedCountN 22880 (centerFull 4) == 38 &&
    (allLt 39 fun k => isInvA 280 (normWordArr k) (invCand 280 (normWordArr k))) &&
    (allLt 8 fun k => isInvA 280 localGenArrs[k]! (invCand 280 localGenArrs[k]!)) &&
    allLt 39 fun k => allLt 39 fun k' => !(decide (k < k')) ||
      (!(eqA 280 (normConj k) (normConj k')) &&
        !(eqA 280 (normConj k) (compA 280 (normConj k') (normConj k'))))

@[expose] def threeChecks (F T : Array (Array Nat)) (E : Enum) : Bool :=
  zChecks && localChecks F && sylowCenterChecks T E && fusionNormChecks

end CFSG.Sporadic.SuzOddCore
