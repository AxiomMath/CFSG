module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
public import CFSG.Quasithin.Vol2.KGFactC31BadScan

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31.Native

@[expose] def refBasisA (τ : ℕ) : List (Array ℕ) :=
  [bEA, b64A, b3A, b16A, b32A].getD τ []

@[expose] def refPrime (τ : ℕ) : ℕ := if τ < 3 then 7 else 5

@[expose] def candWords (τ : ℕ) (kw : List ℤ) : List (List (Array ℕ)) :=
  (refBasisA τ).map fun b => [ruInv (wA kw), b, wA kw]

@[expose] def candsAt (i p : ℕ) : List (List (List (Array ℕ))) :=
  ((candData.getD i []).filter fun c => refPrime c.1 == p).map fun c => candWords c.1 c.2

@[expose] def cosetWords : List (List ℤ) := hWordsZ ++ hWordsA

@[expose] def cosetT0 (i : ℕ) : Array ℕ := if i < 4 then ruZA else ruA0A

@[expose] def cosetLevels (i : ℕ) : List (Array (Array ℕ × Array ℕ)) :=
  if i < 4 then levBlocksI ruLevC 3 else levBlocksI ruLevL 2

@[expose] def scanCount (i : ℕ) (es ps : List ℕ) (p : ℕ) : ℕ :=
  let h := abA (cosetWords.getD i [])
  countWI (badTest ruJoinBase (cosetT0 i) (conjA h (cosetT0 i)) es ps true (candsAt i p))
    (cosetLevels i) [h] [ruInv h]

@[expose] def scanOK (i : ℕ) : Bool :=
  scanCount i [125] [5] 5 == 0 && scanCount i [7] [7] 7 == 0 && scanCount i [13, 29] [13, 29] 0 == 0

end CFSG.Quasithin.KGC31.Ru

end
