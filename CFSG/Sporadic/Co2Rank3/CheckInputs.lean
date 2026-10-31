module

public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public import Certificates.Data.CFSGNative.Co2Rank3.Data
public import CFSG.Sporadic.Co2Cert.Data

@[expose] public section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3.Native

set_option compiler.extract_closed false

def co2DeltaList : List ℕ := co2Rec.stabilizerOrbits.getD 2 []

def co2Nbr : Array (List ℕ) := adjSearch 2300 co2OrigArrs co2DeltaList

def classCount (c : Array ℕ) (v : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 2300 => c[w.val]! = c[v]!).card

def labCount (lab : Array ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 2300 => lab[w.val]! = r).card

def commonCount (l₁ l₂ : List ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 2300 => w.val ∈ l₁ ∧ w.val ∈ l₂).card

def lev1Gens : Array (Array ℕ) := (level1Idx.map fun j => co2StrongArrs[j]!).toArray

def lev2Gens : Array (Array ℕ) := (level2Idx.map fun j => co2StrongArrs[j]!).toArray

def stabGens : Array (Array ℕ) :=
  (stabWords.map (wordA 2300 co2StrongArrs (rawInvs 2300 co2StrongArrs))).toArray

def p0Rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ := orbitSearch 2300 lev1Gens

def stabRec : Array ℕ × Array ℕ × Array ℕ × Array ℕ := orbitSearch 2300 stabGens

def p01Rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ := orbitSearch 2300 lev2Gens

def recOK (gens : Array (Array ℕ)) (rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ)
    (roots : List (ℕ × ℕ)) : Bool :=
  orbitsOK 2300 gens rec.1 rec.2.1 rec.2.2.1 rec.2.2.2 && labelsOK 2300 rec.1 roots &&
    roots.all fun r => labCount rec.1 r.1 == r.2

def co2Rank3OK : Bool :=
  let nbr := co2Nbr
  let c0 := refineIter 2300 nbr (individualize 2300 refineBase 0) 3
  let c1 := refineIter 2300 nbr (individualize 2300 refineBase 1) 3
  let c2 := refineIter 2300 nbr (individualize 2300 refineBase 2) 3
  let c3 := refineIter 2300 nbr (individualize 2300 refineBase 3) 3
  let c4 := refineIter 2300 nbr (individualize 2300 refineBase 4) 3
  let c5 := refineIter 2300 nbr (individualize 2300 refineBase 5) 3
  let c6 := refineIter 2300 nbr (individualize 2300 refineBase 6) 3
  let l0 := p0Rec.1
  let lb := stabRec.1
  let lc := p01Rec.1
  adjOK 2300 co2OrigArrs nbr co2DeltaList &&
    levelIdx co2StrongArrs co2BaseArr 1 == level1Idx &&
    levelIdx co2StrongArrs co2BaseArr 2 == level2Idx &&
    stabWords.all (lettersOK 11) &&
    stabGens.all (fun g => g[0]! == 0 && g[3]! == 3) && stabGens.size == 3 &&
    recOK lev1Gens p0Rec p0Roots && recOK stabGens stabRec stabRoots &&
    recOK lev2Gens p01Rec p01Roots &&
    l0[36]! == 3 && l0[4]! == 3 && l0[5]! == 3 && l0[2]! == 1 && l0[8]! == 1 &&
    listLabelOK 2300 co2DeltaList l0 [3] &&
    listLabelOK 2300 nbr[3]! lb [0, 36, 4, 2] &&
    listLabelOK 2300 nbr[1]! lc [4, 2] &&
    colourLabelOK 2300 c2 lb [0, 1, 2, 3, 4, 5, 36] &&
    classCount c0 0 == 2300 && classCount c1 3 == 891 && classCount c2 1 == 896 &&
    classCount c3 2 == 192 && classCount c4 522 == 10 && classCount c5 360 == 12 &&
    decide c6.toList.Nodup && c6.size == 2300 &&
    commonCount nbr[0]! nbr[3]! == 378 && commonCount nbr[0]! nbr[1]! == 324

end CFSG.Sporadic.Co2Rank3
