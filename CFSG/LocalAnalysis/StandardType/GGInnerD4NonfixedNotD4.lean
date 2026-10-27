module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Lemma4Defs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock


public section

namespace CFSG.StandardType.S2MathAs51586Freeze

open CFSG.Assembly

private theorem ltrd4w1_labelIso_D4 {n' : ℕ} {lab : LargeEvenLabel}
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

theorem nonfixedNotD4_holds : NonfixedNotD4 := by
  intro hRig K V _ _ _ _ _ _ n n' hn hn' hcard Q x hx h hh hne hq hlab
  have hΛD : LargeEvenInLambda2 (⟨.D, 4, n'⟩ : LargeEvenLabel) :=
    ⟨hn', by show 3 ≤ 4; norm_num⟩
  obtain ⟨hm, -, hblock⟩ :=
    TablePThreeKG.orthT_blockLabel hcard hx hh hne hq
      (L := CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h) rfl
  rcases hblock with ⟨-, h3, hlabA⟩ | ⟨-, -, ⟨-, hn2, hlabA⟩ | ⟨hm3, hne', hlabTwA⟩⟩
  · have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn_eq : n = 1 := by omega
      rw [hn_eq] at h3
      norm_num at h3
    have hΛA : LargeEvenInLambda2
        (⟨.A, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
      ⟨hn, by show 1 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1; omega,
        fun _ => hn2⟩
    have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel)
      (⟨.A, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
      (CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h ⧸
        Subgroup.center (CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h)) hΛD hΛA hlab hlabA
    exact absurd (congrArg LargeEvenLabel.tag (ltrd4w1_labelIso_D4 hiso)) (by simp)
  · have hΛA : LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) :=
      ⟨hn, by show 1 ≤ 1; norm_num, fun _ => hn2⟩
    have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel)
      (CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h ⧸
        Subgroup.center (CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h)) hΛD hΛA hlab hlabA
    exact absurd (congrArg LargeEvenLabel.tag (ltrd4w1_labelIso_D4 hiso)) (by simp)
  · have hΛtwA : LargeEvenInLambda2
        (⟨.twA, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
      ⟨hn,
        by show 2 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1; omega,
        by
          show CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1 = 2 → 2 ≤ n
          intro hb
          by_contra hn2'
          exact hne' ⟨by omega, by omega⟩⟩
    have hiso := hRig (⟨.D, 4, n'⟩ : LargeEvenLabel)
      (⟨.twA, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
      (CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h ⧸
        Subgroup.center (CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h)) hΛD hΛtwA hlab hlabTwA
    exact absurd (congrArg LargeEvenLabel.tag (ltrd4w1_labelIso_D4 hiso)) (by simp)

end CFSG.StandardType.S2MathAs51586Freeze

end
