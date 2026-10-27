module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Certificates.Native

open CFSG.Monster.B.Co2.Native

@[expose] def rawInvs (n : Nat) (S : Array (Array Nat)) : Array (Array Nat) :=
  S.map (invCand n)

@[expose] def rawSteps (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i : Nat) :
    Array (Array Nat) :=
  levelSteps S (rawInvs n S) base i

@[expose] def rawLevels (n : Nat) (S : Array (Array Nat)) (base : Array Nat) : Array Level :=
  Array.ofFn (n := base.size) fun i => bfs n base[i.val]! (rawSteps n S base i.val)

@[expose] def rawChainOK (n : Nat) (O S : Array (Array Nat)) (base : Array Nat)
    (W : Array (List Int)) (chunks : Nat) : Bool :=
  let Sinv := rawInvs n S
  let levels := rawLevels n S base
  decide (O.size ≤ S.size) && W.size == S.size &&
    allLt S.size (fun j => isInvA n S[j]! Sinv[j]!) &&
    allLt O.size (fun k => eqA n S[k]! O[k]!) &&
    allLt S.size (fun j => decide (j < O.size) ||
      (lettersOK j W[j]! && eqA n S[j]! (wordA n S Sinv W[j]!))) &&
    allLt S.size (fun j => !(fixesFirst base S[j]! base.size) || eqA n S[j]! (idA n)) &&
    allLt base.size (fun i => decide (base[i]! < n)) &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i) levels[i]!) &&
    allLt base.size (fun i => schreierOK n levels base i (rawSteps n S base i) levels[i]! chunks)

@[expose] def rawOrbitSizes (n : Nat) (S : Array (Array Nat)) (base : Array Nat) : List Nat :=
  (rawLevels n S base).toList.map fun L => L.pts.size

end CFSG.Certificates.Native
