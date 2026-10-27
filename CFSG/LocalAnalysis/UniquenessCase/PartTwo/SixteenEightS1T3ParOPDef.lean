module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin

@[expose] def s16t3PlusCuts (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (m - 2)).filter fun d => d % 2 = 0 ∨ d = m - 2

@[expose] noncomputable def S16t3PlusCensus (K : Type) [Field K] (m : ℕ) : Prop :=
  Nat.card ↥(plusFlagStab K m (s16t3PlusCuts m)) = 3 ^ ((m + 2) / 2) *
      2 ^ (Nat.card ↥(orthElementaryGroup (quadPlus m K))).factorization 2 ∧
    ∀ p ∈ plusFlagStab K m (s16t3PlusCuts m), ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
