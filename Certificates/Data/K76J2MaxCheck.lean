module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public import Certificates.Data.G2ThreeMaxCheck

public section

namespace Certificates.K76J2Max

open CFSG.Monster.B.TwoA.Census Certificates.G2ThreeMax

@[expose] def gensArr : Array (Array ℕ) :=
  #[CFSG.ComponentClassification.J2Cover.autStrong[0]!,
    CFSG.ComponentClassification.J2Cover.autStrong[1]!,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.gensCzArr[0]!,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.gensCzArr[1]!,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.g0Arr]

@[expose] def imgSet (t : Array ℕ) (n : ℕ) : ℕ :=
  (List.range 315).foldl (fun acc i => if n.testBit i then acc ||| 2 ^ t[i]! else acc) 0

@[expose] def act (k n : ℕ) : ℕ := imgSet gensArr[k]! n

@[expose] def root (_ : Unit := ()) : ℕ :=
  (List.range 315).foldl (fun acc i =>
    if CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr[i]! = i then acc ||| 2 ^ i else acc) 0

@[expose] def orbitCert (_ : Unit := ()) : NatCert := natBfs act 5 (root ()) 280

@[expose] def nTabs (c : NatCert) : Array (Array ℕ) :=
  #[permArr c [2], permArr c [3], permArr c [4]]

@[expose] def repOK (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) : Bool :=
  let w := pathWord c 280 r
  let rp := permArr c w
  let c₃ := natBfs (repAct hp rp) 4 0 280
  w.all (· < 5) && applyW c w 0 == r &&
    natCertOK (repAct hp rp) 4 (fun u => decide (u < 280)) 0 c₃ &&
    c₃.pts.toList.mergeSort (fun a b => decide (a ≤ b)) == List.range 280

@[expose] def check (_ : Unit := ()) : Bool :=
  let c := orbitCert ()
  let hp := nTabs c
  let orbs := orbitSearch (hAct hp) 3 280
  natCertOK act 5 (fun u => decide (u < 2 ^ 315)) (root ()) c && c.pts.size == 280 &&
    (List.range 3).all (fun s => tabOf c (s + 2) 0 == 0) && okOrbs hp 280 orbs &&
    orbs.all fun t => t.1 == 0 || repOK c hp t.1

end Certificates.K76J2Max
