module

public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank

@[expose] def OmegaEightMinusQPlus : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K + 1 →
      3 ≤ localRank p (StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))

theorem omegaEightMinusNotTwo_of_qPlus (hQ : OmegaEightMinusQPlus) : OmegaEightMinusNotTwo := by
  intro K _ _ _ b c hirr p hp hp5
  have hp2 : p ≠ 2 := by omega
  by_cases h1 : p ∣ Nat.card K - 1
  · have hKu : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      exact h1
    have := PartTwo.KFacts.KS21LocalRank.le_localRank_statedOmegaMinus_torus hp hp2 hKu b c
    omega
  · by_cases h2 : p ∣ Nat.card K + 1
    · have := hQ K b c hirr p hp hp2 h2
      omega
    · have := KFU.localRank_statedProj_statedOmegaMinus_four_le_one hirr hp hp2 h1 h2
      omega

end CFSG.RankThree.PartOne
