module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Local
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329ClassicalY
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329ClassicalO3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Glue
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Nineteen
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.Open (StatedLieTag)

@[expose] def k329LieTypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    CFSG.Open.IsQuasisimple ↥(CFSG.Open.genFittingFStar G) →
    CFSG.Open.IsKGroup (↥(CFSG.Open.genFittingFStar G) ⧸
      Subgroup.center ↥(CFSG.Open.genFittingFStar G)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 →
    ∀ X : Subgroup G, X ≤ CFSG.Open.genFittingFStar G → LieModel ↥X .PSU 3 2 3 →
      ∃ (t : StatedLieTag) (n r e : ℕ),
        LieModel (↥(CFSG.Open.genFittingFStar G) ⧸
          Subgroup.center ↥(CFSG.Open.genFittingFStar G)) t n r e ∧ r ≠ 3

theorem k329_of_leaves
    (hLie : k329LieTypeStatement) (hHeavy : k329HeavyRankStatement)
    (hA : k329U38LocalFactsStatement)
    (hCY : k329ClassicalYStatement) (hCO : k329ClassicalO3Statement)
    (hEY : k329ExceptionalYStatement) (hEO : k329ExceptionalO3Statement)
    (h19 : k329NineteenFreeStatement)
    : K329 := by
  have hRed := k329TwoCentralizerReduction_of_parts
  have hD := k329_nineteen_dvd
  have hEq := k329_eq_of_psu38
  intro G _ _ hQ hK hm3 X P hXK hX hP hΓ
  obtain ⟨t, n, r, e, hLieS, hr⟩ := hLie G hQ hK hm3 X hXK hX
  by_cases htH : t ∈ k329HeavyTags
  · exfalso
    have h4 := hHeavy _ hQ t htH n r e hLieS hr
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h4
    have h3 := (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
      (le_top : CFSG.Open.genFittingFStar G ≤ ⊤)).trans hm3
    omega
  obtain ⟨⟨u, hu⟩, ⟨z, hz⟩⟩ := hRed hA G hQ X P hXK hX hP hΓ
  have hS : IsSimpleGroup (↥(CFSG.Open.genFittingFStar G) ⧸
      Subgroup.center ↥(CFSG.Open.genFittingFStar G)) := hQ.2
  have hU38 := k329CrossCharacteristicTwoCentralizer_of_leaves hCY hCO hEY hEO h19 _ hS t n r e
    htH hLieS hr (hD G X hXK hX) u z hu hz
  exact hEq G hQ X hXK hX hU38

theorem k329_of_inputs
    (hLie : k329LieTypeStatement) (hHeavy : k329HeavyRankStatement)
    (hEY : k329ExceptionalYStatement) (hEO : k329ExceptionalO3Statement) : K329 :=
  k329_of_leaves hLie hHeavy k329U38LocalFacts_of_parts
    k329_classicalY k329_classicalO3 hEY hEO k329_nineteenFree

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
