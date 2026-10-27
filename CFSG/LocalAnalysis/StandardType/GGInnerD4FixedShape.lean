module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Lemma4Defs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2


public section

namespace CFSG.StandardType.S2MathAs51586Freeze

open CFSG.Assembly

private theorem ltrd4w2_labelIso_D4 {n' : ℕ} {lab : LargeEvenLabel}
    (hiso : GGLabelIso (⟨.D, 4, n'⟩ : LargeEvenLabel) lab) : lab = ⟨.D, 4, n'⟩ := by
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h.symm
  · obtain ⟨h1, -⟩ := h
    rcases h1 with h1 | h1 <;> exact absurd h1 (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.rank h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨-, h1⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)

theorem fixedD4Shape_holds : FixedD4Shape := by
  intro hRig K V _ _ _ _ _ _ n n' hn hn' hcard Q hQ x hx F hFq hFle hFn L hL hlab
  classical
  obtain ⟨s, hs, hcases⟩ :=
    CFSG.StandardType.TablePThreeKG.orthT_fixedLabel hcard hQ hx hFq hFle hFn hL
  have hΛD : LargeEvenInLambda2 (⟨.D, 4, n'⟩ : LargeEvenLabel) :=
    ⟨by show 1 ≤ n'; omega, by show 3 ≤ 4; norm_num⟩
  have hmain : s = 4 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧ n' = n := by
    rcases hcases with ⟨h4s, hplus, hlab'⟩ | ⟨h4s, hnplus, hlab'⟩ |
      ⟨hs3, hplus, hlab'⟩ | ⟨hs3, hnplus, hlab'⟩ | ⟨hs2, hnplus, hlab'⟩ |
      ⟨hs2, hplus, hn2, hlab'⟩
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 3 ≤ s; omega⟩
      have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.D, s, n⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) hΛD hΛ' hlab hlab'
      have h := ltrd4w2_labelIso_D4 hiso
      exact ⟨congrArg LargeEvenLabel.rank h, hplus, (congrArg LargeEvenLabel.n h).symm⟩
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 2 ≤ s; omega⟩
      have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.twD, s, n⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (ltrd4w2_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 1 ≤ 3; norm_num,
          by show (3 : ℕ) = 1 → 2 ≤ n; omega⟩
      have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.A, 3, n⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (ltrd4w2_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 2 ≤ 3; norm_num,
          by show (3 : ℕ) = 2 → 2 ≤ n; omega⟩
      have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.twA, 3, n⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (ltrd4w2_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ 2 * n; omega, by show 1 ≤ 1; norm_num,
          by show (1 : ℕ) = 1 → 2 ≤ 2 * n; omega⟩
      have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.A, 1, 2 * n⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (ltrd4w2_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 1 ≤ 1; norm_num, fun _ => hn2⟩
      have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (ltrd4w2_labelIso_D4 hiso)) (by simp)
  obtain ⟨hs4, hplus, hn'n⟩ := hmain
  have hdim8 : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V)) = 8 := by
    omega
  have hFeq : F = CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (x : V ≃ₗ[K] V) := by
    have hRnd : (QuadraticMap.polarBilin
        (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V)).subtype)).Nondegenerate :=
      hx.polarBilin_fixed_nondegenerate
    have hC : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V)).subtype))) :=
      CFSG.RankThree.PartOne.KCOrthogonal.orthogonal_regular_space_derived_quasisimple
        (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V)).subtype) hRnd (by omega)
        (by
          intro h
          rcases h with ⟨h3, -⟩ | ⟨⟨h4, -⟩, -⟩ <;> omega)
        (by rintro ⟨h4, -⟩; omega)
    exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_eq_supportedFixedDerived hx hFq hFle hFn hC
  exact ⟨hn'n, hdim8, hplus, hFeq⟩

end CFSG.StandardType.S2MathAs51586Freeze

end
