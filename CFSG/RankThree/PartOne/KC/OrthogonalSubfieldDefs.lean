module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.RankThree.PartOne

open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.LocalRank

@[expose] def OrthogonalSubfieldCoreClause : Prop :=
  ∀ (c : StatedLieTag) (n ℓ f p : ℕ), (c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) →
    StatedLieAdmissible c n ℓ (f / p) → p.Prime → 3 < p → p ≠ ℓ → p ∣ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ σ : K ≃+* K, orderOf σ = p → Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) →
    match c with
    | .POmegaOdd => ∀ g : similarityPairs (coordinateQuadOdd n K), g.val.left = 1 →
        g.val.right = σ →
        ∀ B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))),
          OuterAutomorphisms.inner _ ≤ B → matrixProjectiveConjugationHom _ g ∈ B →
            inSubgroup (aschbacherSolvableCore p)
              (B ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom _ g}) = ⊥
    | .POmegaPlus => ∀ g : similarityPairs (coordinateQuadPlus n K), g.val.left = 1 →
        g.val.right = σ →
        ∀ B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))),
          OuterAutomorphisms.inner _ ≤ B → matrixProjectiveConjugationHom _ g ∈ B →
            inSubgroup (aschbacherSolvableCore p)
              (B ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom _ g}) = ⊥
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (b c' : semilinearFixedSubfield σ),
        (∀ s : semilinearFixedSubfield σ, s ^ 2 + b * s + c' ≠ 0) →
        ∀ g : similarityPairs (coordinateQuadMinus n K hn (b : K) (c' : K)), g.val.left = 1 →
          g.val.right = σ →
          ∀ B : Subgroup (MulAut
              (matrixProjectiveDerived (coordinateQuadMinus n K hn (b : K) (c' : K)))),
            OuterAutomorphisms.inner _ ≤ B → matrixProjectiveConjugationHom _ g ∈ B →
              inSubgroup (aschbacherSolvableCore p)
                (B ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom _ g}) = ⊥
    | _ => False

end CFSG.RankThree.PartOne
