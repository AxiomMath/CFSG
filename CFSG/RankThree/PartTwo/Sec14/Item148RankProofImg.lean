module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepRank
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Steps


@[expose] def Step148RankImgLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2;
          Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y J

@[expose] def Step148RankImgGe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Ten A Y K J ∨ Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        letI := ker148_normal hY.2
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y)

end Steps

variable {G : Type} [Group G] [Finite G]

theorem img148_le_of_lift148Eq {A Y K J : Subgroup G} [(ker148 A Y).Normal]
    (hKY : K ≤ Y) (hKΔ : K = deltaZero A (lB A) K) (hEq : Lift148Eq A Y K J) :
    img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
  have hEq' : img148 A Y K = img148 A Y J := hEq
  rw [← hEq']
  refine img148_mono ?_
  rw [hKΔ]
  exact deltaZero_mono148 (hKΔ ▸ hKY)

theorem step148RankImg_of
    (hLe : Step148RankImgLe) (hGe : Step148RankImgGe) : Step148RankImg := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hA
  have := ker148_normal hY.2
  refine le_antisymm (hLe G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hA)
    ?_
  rcases halt with hEq | hTen | hField
  · have hKY : K ≤ Y :=
      (le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1).trans inf_le_left
    exact img148_le_of_lift148Eq hKY hP.2.2.2.2.2.2.1 hEq
  · exact hGe G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ (Or.inl hTen) hA
  · exact hGe G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ (Or.inr hField) hA

end CFSG.RankThree.PartTwo.Sec14
