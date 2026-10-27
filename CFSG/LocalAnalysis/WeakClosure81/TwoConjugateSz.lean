module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def TwoConjugateGenerationSz : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 1 < n → CFSG.Quasithin.IsSz n S →
    ∀ A : Subgroup S, CFSG.Open.IsElemAbelian 2 A → 2 < Nat.card A →
      ∃ g : S, A ⊔ CFSG.Quasithin.conjSubgroup A g = ⊤

theorem twoConjugateGeneration_of_sz
    (hSz : TwoConjugateGenerationSz) : TwoConjugateGeneration := by
  intro S _ _ n hn hS A hA hcard
  rcases hS with hS | hS
  · exact CFSG.LocalAnalysis.WeakClosure81.TwoConjL2.twoConjugateGeneration_of_isPSL hS hA hcard
  · exact hSz S n hn hS A hA hcard

end CFSG.LocalAnalysis.WeakClosure81.SevenK
