module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Step74
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Step75

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem step75 (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (hSE : StronglyEmbeddedFive) : Step75 k :=
  step75_of_coverActsTriviallyOnSmall k fun _ hH =>
    coverActsTriviallyOnSmall_of_stronglyEmbeddedFive k h5 hH hSE

theorem step74_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (hno : KIDExcluded k)
    (hSE : StronglyEmbeddedFive) : Step74 k :=
  step74_of_pPrimeCore_eq_bot k fun _ hH =>
    (good_of_stronglyEmbeddedFive_of_kIDExcluded k h5 hno hH hSE (step75 k h5 hSE)).1

theorem step74 (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (h3 : 3 ∉ CFSG.Open.uniqueFourBeta G)
    (hSE : StronglyEmbeddedFive) : Step74 k :=
  step74_of_kIDExcluded k h5 (k.kIDExcluded_of_not_mem_beta h3) hSE

theorem step76C_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (hno : KIDExcluded k)
    (hSE : StronglyEmbeddedFive) : Step76C k :=
  step76C_of_centralizerHasPElementOutside k fun _ hH =>
    (good_of_stronglyEmbeddedFive_of_kIDExcluded k h5 hno hH hSE (step75 k h5 hSE)).2

theorem normalizer_le_of_stronglyEmbeddedFive_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : KIDExcluded k) (hSE : StronglyEmbeddedFive)
    {Y : Subgroup G} (hY : Y ≠ ⊥) (hYM : Y ≤ k.M)
    (hrank : 2 ≤ CFSG.Open.pRank k.p (k.M ⊓ Subgroup.normalizer (Y : Set G)))
    (hQ : CFSG.Open.pCoreOf 2 k.M ⊓ Subgroup.normalizer (Y : Set G) ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ k.M :=
  normalizer_le_of_step74 k (step74_of_kIDExcluded k h5 hno hSE) hY hYM hrank hQ

theorem normalizer_le_of_stronglyEmbeddedFive (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (h3 : 3 ∉ CFSG.Open.uniqueFourBeta G) (hSE : StronglyEmbeddedFive)
    {Y : Subgroup G} (hY : Y ≠ ⊥) (hYM : Y ≤ k.M)
    (hrank : 2 ≤ CFSG.Open.pRank k.p (k.M ⊓ Subgroup.normalizer (Y : Set G)))
    (hQ : CFSG.Open.pCoreOf 2 k.M ⊓ Subgroup.normalizer (Y : Set G) ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ k.M :=
  normalizer_le_of_stronglyEmbeddedFive_of_kIDExcluded k h5 (k.kIDExcluded_of_not_mem_beta h3)
    hSE hY hYM hrank hQ

theorem conclusion76_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (hno : KIDExcluded k)
    (hSE : StronglyEmbeddedFive) : Conclusion76 k.M k.p :=
  conclusion76_of_steps k (step74_of_kIDExcluded k h5 hno hSE).toWeak (step75 k h5 hSE)
    (step72L k) (step76C_of_kIDExcluded k h5 hno hSE)

theorem conclusion76 (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (h3 : 3 ∉ CFSG.Open.uniqueFourBeta G)
    (hSE : StronglyEmbeddedFive) : Conclusion76 k.M k.p :=
  conclusion76_of_kIDExcluded k h5 (k.kIDExcluded_of_not_mem_beta h3) hSE

end Sec7Core4

theorem conclusion76 (c : Counterexample4 G) {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (hSE : StronglyEmbeddedFive) : Conclusion76 c.S.M p :=
  (c.toSec7Core4 hp).conclusion76 (c.five_le_of_mem_sigma hp) c.three_not_mem_beta hSE

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
