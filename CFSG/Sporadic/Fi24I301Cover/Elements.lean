module

public import Certificates.Certificate810307
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.Sporadic.Fi24I301Cover

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th CFSG.Sporadic.Fi24I301
open CFSG.Sporadic.Fi24 (J)

section Check

theorem noAltForm : ∀ c : Fin 10 → ZMod 3,
    (∀ k : Fin 2, nMat k * altMat c * (nMat k).transpose = altMat c) → c = 0 :=
  Certificates.certificate810307.1

theorem noLinForm : ∀ q : Fin 5 → ZMod 3, (∀ k : Fin 2, (nMat k).mulVec q = q) → q = 0 :=
  Certificates.certificate810307.2.1

theorem nJ_conj
    {k : ℕ} (hk : k < 2) {i : ℕ} (hi : i < 5) :
    nJ k * xJ i * (nJ k)⁻¹ = prodElt ((nMats[k]!)[i]!) :=
  Certificates.certificate810307.2.2 k hk i hi

end Check

end CFSG.Sporadic.Fi24I301Cover
