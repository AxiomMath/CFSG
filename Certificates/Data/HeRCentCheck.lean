module

public import Certificates.Data.HePresCheck
public import Certificates.Data.HeRCentData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.CertPChainData

public section

namespace CFSG.ComponentClassification.AS81.HePres.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def heSeedArrs : Array (Array Nat) :=
  #[CFSG.Sporadic.HeldB.heGen 0, CFSG.Sporadic.HeldB.heGen 1]

@[expose] def heGenArrs8 : Array (Array Nat) :=
  ((List.range 8).map fun i =>
    wordA 8330 heSeedArrs (heSeedArrs.map (invCand 8330)) (hePiHeWords.getD i [])).toArray

@[expose] def heWordArr (w : List Nat) : Array Nat :=
  wordArrW 8330 heGenArrs8 (heGenArrs8.map (invCand 8330)) (ofCodes w)

@[expose] def commArr (n : Nat) (a b : Array Nat) : Array Nat :=
  compA n a (compA n b (compA n (invCand n a) (invCand n b)))

@[expose] def fixCountA (n : Nat) (t : Array Nat) : Nat :=
  (List.range n).countP fun i => t[i]! == i

@[expose] def commutesA (n : Nat) (t u : Array Nat) : Bool :=
  eqA n (compA n t u) (compA n u t)

@[expose] def heGenArrsOK : Bool :=
  (List.range 8).all fun i =>
    isInvA 8330 (heGenArrs8.getD i #[]) ((heGenArrs8.map (invCand 8330)).getD i #[])

@[expose] def heRInvolOK : Bool :=
  let r₁ := heWordArr (heRWords.getD 0 [])
  let r₂ := heWordArr (heRWords.getD 1 [])
  let r₃ := compA 8330 r₁ r₂
  eqA 8330 (compA 8330 r₁ r₁) (idA 8330) && eqA 8330 (compA 8330 r₂ r₂) (idA 8330) &&
    commutesA 8330 r₁ r₂ && !eqA 8330 r₁ (idA 8330) && !eqA 8330 r₂ (idA 8330) &&
    !eqA 8330 r₃ (idA 8330) && fixCountA 8330 r₁ == 346 && fixCountA 8330 r₂ == 346 &&
    fixCountA 8330 r₃ == 346

@[expose] def heRWitOK : Bool :=
  let y := heWordArr heRWitWord
  commutesA 8330 y (heWordArr (heRWords.getD 0 [])) &&
    !commutesA 8330 y (heWordArr (heRWords.getD 1 []))

@[expose] def heRCentOK : Bool :=
  let r₁ := heWordArr (heRWords.getD 0 [])
  let r₂ := heWordArr (heRWords.getD 1 [])
  heRCentWords.length == 4 && heRCentWords.all fun w =>
    let u := heWordArr w
    isInvA 8330 u (invCand 8330 u) && commutesA 8330 u r₁ && commutesA 8330 u r₂

@[expose] def heRChainOrig : Array (Array Nat) :=
  #[commArr 8330 (heWordArr (heRCentWords.getD 0 [])) (heWordArr (heRCentWords.getD 1 [])),
    commArr 8330 (heWordArr (heRCentWords.getD 2 [])) (heWordArr (heRCentWords.getD 3 []))]

@[expose] def buildStrong (n : Nat) (O : Array (Array Nat)) (W : Array (List Int)) :
    Array (Array Nat) :=
  (List.range W.size).foldl (fun S j =>
    S.push (if j < O.size then O[j]! else wordA n S (S.map (invCand n)) W[j]!)) #[]

@[expose] def heRStrong : Array (Array Nat) := buildStrong 8330 heRChainOrig heRChainWords

@[expose] def heRChainBaseArr : Array Nat := (heRChainBase.map Fin.val).toArray

end CFSG.ComponentClassification.AS81.HePres.Native
