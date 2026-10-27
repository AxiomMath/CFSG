module

public import CFSG.RankThree.PartOne.AUTSL.FrobPair
public import CFSG.LieType.Universal.Spin.Twisted.Short
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

namespace CFSG.StandardType.KGOm

open CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin.Twisted

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

@[expose] noncomputable def minusSemi (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : ℕ) (y : Vm n K) : Vm n K :=
  (reindexVectorEquiv (minusIndexEquiv n hn)).symm
    (coordinateSemilinearMap (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k).val
      (reindexVectorEquiv (minusIndexEquiv n hn) y))

theorem reindex_minusSemi (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) :
    reindexVectorEquiv (minusIndexEquiv n hn) (minusSemi hn hirr k y) =
      coordinateSemilinearMap (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k).val
        (reindexVectorEquiv (minusIndexEquiv n hn) y) :=
  LinearEquiv.apply_symm_apply _ _

end CFSG.StandardType.KGOm
