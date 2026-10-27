module

public import CFSG.RankThree.PartOne.KF.ClsExcE

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank

@[expose] def KF123ExcG2NoRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ 2 ^ f - 1 → localRank p X ≤ 1

@[expose] def KF123ExcD4NoRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ 2 ^ f - 1 → localRank p X ≤ 1

@[expose] def KF123ExcTwF4NoRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), Blueprint.ReeTitsModel X .twistedF4 2 f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ 2 ^ f - 1 → localRank p X ≤ 1

theorem kf123ClassifyTag_G2 (hG2 : KF123ExcG2NoRankTwo) : KF123ClassifyTag .G2 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := (show n = 0 ∧ 3 ≤ 2 ^ f from hadm.2.2).1
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  by_cases hdvd : p ∣ 2 ^ f - 1
  · exact ⟨2, by norm_num, by norm_num, by norm_num, f, hf1, hdvd, hmodel⟩
  · exfalso
    have hle := hG2 (↥L ⧸ Subgroup.center ↥L) f hch p h.prime h.five_le hdvd
    have hrank := h.localRank_quot_eq
    omega

theorem kf123ClassifyTag_trialityD4 (hD4 : KF123ExcD4NoRankTwo) :
    KF123ClassifyTag .trialityD4 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  by_cases hdvd : p ∣ 2 ^ f - 1
  · exact ⟨3, by norm_num, by norm_num, by norm_num, f, hf1, hdvd, hmodel⟩
  · exfalso
    have hle := hD4 (↥L ⧸ Subgroup.center ↥L) f hch p h.prime h.five_le hdvd
    have hrank := h.localRank_quot_eq
    omega

theorem kf123ClassifyTag_twistedF4 (hF4 : KF123ExcTwF4NoRankTwo) :
    KF123ClassifyTag .twistedF4 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := (show n = 0 ∧ 2 = 2 ∧ Odd f ∧ 3 ≤ f from hadm.2.2).1
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hR : Blueprint.ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hR
    · exact absurd ht (by decide)
  by_cases hdvd : p ∣ 2 ^ f - 1
  · exact ⟨4, by norm_num, by norm_num, by norm_num, f, hf1, hdvd, hmodel⟩
  · exfalso
    have hle := hF4 (↥L ⧸ Subgroup.center ↥L) f hR p h.prime h.five_le hdvd
    have hrank := h.localRank_quot_eq
    omega

end CFSG.RankThree.PartOne
