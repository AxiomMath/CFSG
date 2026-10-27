module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor lieSylowExponent lie_casework)
open CFSG.ComponentClassification.CatLeafProof (lieOrderFormulasInput)

@[expose] def OddLieFieldThree : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n r f : ℕ), r ≠ 2 → StatedLieAdmissible t n r f →
    LieModel X t n r f →
    (LieModel X .PSL 3 3 1 ∨ LieModel X .PSU 3 3 1 ∨ LieModel X .PSL 4 3 1 ∨
      LieModel X .PSU 4 3 1 ∨ LieModel X .G2 0 3 1 ∨ LieModel X .PSp 2 3 1 ∨
      LieModel X .PSp 3 3 1) →
    r ^ f = 3

private theorem f_eq_one_of_lieModel_three_one
    {X : Type} [Group X] {t t₂ : StatedLieTag} {n n₂ f : ℕ}
    (hO : LieOrderFormulasInput)
    (hadm : StatedLieAdmissible t n 3 f) (hmodel : LieModel X t n 3 f)
    (hX₂ : LieModel X t₂ n₂ 3 1)
    (hadm₂ : StatedLieAdmissible t₂ n₂ 3 1)
    (hle : lieSylowExponent t₂ n₂ ≤ 10)
    (hno : ∀ t n f, StatedLieAdmissible t n 3 f → 2 ≤ f →
      lieSylowExponent t n * f = lieSylowExponent t₂ n₂ →
      lieOrderNumerator t n (3 ^ f) * lieOrderDivisor t₂ n₂ 3 ≠
        lieOrderNumerator t₂ n₂ 3 * lieOrderDivisor t n (3 ^ f)) : f = 1 := by
  obtain ⟨-, hmul2, hfac2⟩ := hO X t₂ n₂ 3 1 hadm₂ hX₂
  have hmul2' :
      Nat.card X * lieOrderDivisor t₂ n₂ 3 = lieOrderNumerator t₂ n₂ 3 := by
    simpa using hmul2
  obtain ⟨-, hmul1, hfac1⟩ := hO X t n 3 f hadm hmodel
  have hNf : lieSylowExponent t n * f = lieSylowExponent t₂ n₂ := by
    rw [← hfac1, hfac2, mul_one]
  have hcross :
      lieOrderNumerator t n (3 ^ f) * lieOrderDivisor t₂ n₂ 3 =
        lieOrderNumerator t₂ n₂ 3 * lieOrderDivisor t n (3 ^ f) := by
    rw [← hmul1, ← hmul2']
    ring
  by_contra hgoal
  have hf : 2 ≤ f := by
    have := hadm.2.1
    omega
  exact absurd hcross (hno t n f hadm hf hNf)

theorem oddLieFieldThree :
    OddLieFieldThree := by
  intro X _ t n r f hr hadm hmodel hX
  rcases hX with hX2 | hX2 | hX2 | hX2 | hX2 | hX2 | hX2
  all_goals
    have hr3 : r = 3 :=
      CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds X t n r f
        _ _ 3 1 hr (by norm_num) hmodel hX2
    subst r
    rw [f_eq_one_of_lieModel_three_one lieOrderFormulasInput hadm hmodel hX2
      (by norm_num [StatedLieAdmissible]) (by decide) (by
        intro t' n' f' hadm' hf' hNf'
        have hb' : lieSylowExponent t' n' * f' ≤ 10 := by
          rw [hNf']
          decide
        rcases lie_casework hadm' hb' with
          ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn0, hf1, hf2⟩
        · rcases ht with rfl | rfl <;>
            simp only [lieSylowExponent] at hb'
          all_goals
            interval_cases n' <;> interval_cases f' <;> decide
        · rcases ht with rfl | rfl <;>
            simp only [lieSylowExponent] at hb'
          all_goals
            interval_cases n' <;> interval_cases f' <;> decide
        · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
          subst n'
          cases t' <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
            simp only [lieSylowExponent] at hb' <;>
            interval_cases f' <;> decide)]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
