module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

@[expose] def E6LeviThreeToralBar : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ], ℓ ≠ 3 →
    (letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) →
    ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      (kernelRoots (rootCharHom a)).ncard ∈ ({22, 24, 40} : Set ℕ) →
      ∀ X : Subgroup (ModGL Tag.E6 L), IsElemAbelian 3 X → X ≤ toralRootGroup Tag.E6 L a →
        E6AdToral X

end CFSG.StandardType.SCFourCover

end
