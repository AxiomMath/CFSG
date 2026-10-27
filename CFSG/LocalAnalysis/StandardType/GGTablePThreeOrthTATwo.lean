module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLift
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

section TATwo

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.ClassicalGroups.Orthogonal

private theorem orthTATwo_one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [hK] at h2
  by_contra hn
  have hn0 : n = 0 := by omega
  rw [hn0] at h2
  exact absurd h2 (by norm_num)

private theorem orthTATwo_lambda2_A {r n : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (h : r = 1 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.A, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private theorem orthTATwo_lambda2_twA {r n : ℕ} (hn : 1 ≤ n) (hr : 2 ≤ r)
    (h : r = 2 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.twA, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private theorem orthTATwo_lambda2_D {s n : ℕ} (hn : 1 ≤ n) (hs : 3 ≤ s) :
    LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hs⟩

private theorem orthTATwo_lambda2_twD {s n : ℕ} (hn : 1 ≤ n) (hs : 2 ≤ s) :
    LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hs⟩

private theorem orthTATwo_lambda2 {R : Type} [Group R] {k : ℕ}
    (hlab : GGHasLabel (⟨.A, 2, k⟩ : LargeEvenLabel) R) :
    LargeEvenInLambda2 (⟨.A, 2, k⟩ : LargeEvenLabel) := by
  obtain ⟨K, hF, hFin, hcard, -⟩ := hlab
  haveI := hF
  haveI := hFin
  exact orthTATwo_lambda2_A (orthTATwo_one_le_of_card hcard) (by norm_num) (by intro h; omega)

private theorem orthTATwo_iso {k : ℕ} {lab0 : LargeEvenLabel}
    (h : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) lab0) : lab0 = ⟨.A, 2, k⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · rcases h.1 with h1 | h1
    · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.B from h1) (by decide)
    · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.C from h1) (by decide)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.D from
      congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (show (2 : ℕ) = 3 from congrArg LargeEvenLabel.rank h.1) (by decide)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twD from
      congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twA from
      congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twD from
      congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (show (2 : ℕ) = 1 from congrArg LargeEvenLabel.rank h.2) (by decide)

private theorem orthTATwo_center {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {J' : Subgroup (ProjOrthDerived Q)} {x : ↥(orthDerived Q)} (hx : x ≠ 1)
    (hscal : (scalars K V).subgroupOf (orthDerived Q) = ⊥)
    (hxJ' : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x ∈ J')
    (hle : J' ≤ centralizerImage Q (x : V ≃ₗ[K] V)) :
    Subgroup.center J' ≠ ⊥ := by
  intro hbot
  have hmem : (⟨QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x, hxJ'⟩ : ↥J') ∈
      Subgroup.center ↥J' := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : ProjOrthDerived Q) *
        QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x =
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x * (y : ProjOrthDerived Q)
    have hy : (y : ProjOrthDerived Q) ∈
        ((isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := hle y.2
    rw [Subgroup.mem_map] at hy
    obtain ⟨g, hg, hgy⟩ := hy
    have hgx : ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
      Subgroup.mem_subgroupOf.mp hg
    have hcomm : x * g = g * x := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact ((mem_isometryCentralizer.mp hgx).2 v).symm
    have hq : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x *
          QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) g =
        QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) g *
          QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x := by
      calc QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x *
            QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) g
          = QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) (x * g) :=
            (map_mul _ _ _).symm
        _ = QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) (g * x) := by rw [hcomm]
        _ = QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) g *
            QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x := map_mul _ _ _
    rw [← hgy]
    exact hq.symm
  have hxne : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [hscal, Subgroup.mem_bot] at h1
    exact hx h1
  have h1 : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x = 1 := by
    have h2 : (⟨QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x, hxJ'⟩ : ↥J') ∈
        (⊥ : Subgroup ↥J') := hbot ▸ hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h2)
  exact hxne h1

end TATwo

theorem orthT_A2
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {k : ℕ} (hlab : GGHasLabel ⟨.A, 2, k⟩ (J' ⧸ Subgroup.center J')) :
    Subgroup.center J' ≠ ⊥ := by
  have hΛ₂ : LargeEvenInLambda2 (⟨.A, 2, k⟩ : LargeEvenLabel) := orthTATwo_lambda2 hlab
  obtain ⟨x, Â, hδx, hxodd, hxne, hxA, hAea, hAcard, hAnorm, hAker, hcomp, hfix, hdisj⟩ :=
    orthT_lift hQ hT hR hĀI
  obtain ⟨U, hU3, -⟩ := hT
  have hVpos : 0 < Module.finrank K V := by
    have hle : Module.finrank K U ≤ Module.finrank K V := Submodule.finrank_le U
    rw [hU3] at hle
    omega
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) hVpos
  have hscal : (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q) = ⊥ :=
    CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  have hn1 : 1 ≤ n := orthTATwo_one_le_of_card hK
  rcases hdisj with ⟨h, hh, hne1, hq, hJ'L⟩ | ⟨F, hFq, hFle, hFn, hJ'F⟩
  · rw [hJ'L] at hlab ⊢
    obtain ⟨hm2, h3m, hblock⟩ := orthT_blockLabel hK hxodd hh hne1 hq rfl
    rcases hblock with ⟨-, hdvd, hlabA⟩ | ⟨-, -, hblockSd⟩
    · have hn2 : 2 ≤ n := by
        by_contra hn
        have hn1' : n = 1 := by omega
        rw [hn1'] at hdvd
        exact absurd hdvd (by norm_num)
      have hΛblk : LargeEvenInLambda2
          (⟨.A, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_A hn1 (by omega) (fun _ => hn2)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel)
          (⟨.A, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabA
      have hm1 : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1 = 2 :=
        congrArg LargeEvenLabel.rank (orthTATwo_iso hiso)
      have hm3 : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 := by omega
      have h3dvd : 3 ∣ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h :=
        ⟨1, by omega⟩
      exact orthTATwo_center hxne hscal (h3m h3dvd)
        CFSG.RankThree.PartOne.KCOrthogonal.componentImage_le_centralizerImage
    · rcases hblockSd with ⟨-, hn2, hlabA1⟩ | ⟨hm3, hnot, hlabTwA⟩
      · have hΛblk : LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) :=
          orthTATwo_lambda2_A hn1 (by norm_num) (fun _ => hn2)
        have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabA1
        exact absurd (show (1 : ℕ) = 2 from congrArg LargeEvenLabel.rank (orthTATwo_iso hiso))
          (by decide)
      · have hΛblk : LargeEvenInLambda2
            (⟨.twA, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ :
              LargeEvenLabel) := by
          refine orthTATwo_lambda2_twA hn1 (by omega) ?_
          intro hr
          have hm3' : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 := by omega
          by_contra hn
          exact hnot ⟨by omega, hm3'⟩
        have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel)
            (⟨.twA, CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ :
              LargeEvenLabel) :=
          ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabTwA
        exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.A from
          congrArg LargeEvenLabel.tag (orthTATwo_iso hiso)) (by decide)
  · rw [hJ'F] at hlab
    obtain ⟨s, -, hcase⟩ := orthT_fixedLabel hK hQ hxodd hFq hFle hFn rfl
    rcases hcase with ⟨h4, -, hlabD⟩ | ⟨h4, -, hlabTwD⟩ | ⟨hs3, -, hlabA3⟩ |
      ⟨hs3, -, hlabTwA3⟩ | ⟨hs2, -, hlabA1'⟩ | ⟨hs2, -, hn2, hlabA1n⟩
    · have hΛblk : LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_D hn1 (by omega)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.D, s, n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabD
      exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from
        congrArg LargeEvenLabel.tag (orthTATwo_iso hiso)) (by decide)
    · have hΛblk : LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_twD hn1 (by omega)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.twD, s, n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabTwD
      exact absurd (show LargeEvenLieTag.twD = LargeEvenLieTag.A from
        congrArg LargeEvenLabel.tag (orthTATwo_iso hiso)) (by decide)
    · have hΛblk : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_A hn1 (by norm_num) (by intro h; omega)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.A, 3, n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabA3
      exact absurd (show (3 : ℕ) = 2 from congrArg LargeEvenLabel.rank (orthTATwo_iso hiso))
        (by decide)
    · have hΛblk : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_twA hn1 (by norm_num) (by intro h; omega)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabTwA3
      exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.A from
        congrArg LargeEvenLabel.tag (orthTATwo_iso hiso)) (by decide)
    · have hΛblk : LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_A (by omega) (by norm_num) (by intro h; omega)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabA1'
      exact absurd (show (1 : ℕ) = 2 from congrArg LargeEvenLabel.rank (orthTATwo_iso hiso))
        (by decide)
    · have hΛblk : LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) :=
        orthTATwo_lambda2_A hn1 (by norm_num) (fun _ => hn2)
      have hiso : GGLabelIso (⟨.A, 2, k⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hΛ₂ hΛblk hlab hlabA1n
      exact absurd (show (1 : ℕ) = 2 from congrArg LargeEvenLabel.rank (orthTATwo_iso hiso))
        (by decide)

end CFSG.StandardType.TablePThreeKG

end
