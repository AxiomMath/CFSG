module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLift
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTRank
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownLevel
import CFSG.Assembly.OrderReductions.Helpers

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

section OrthAux

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

private theorem orthTAOne_k {R : Type} [Group R] {k : ℕ}
    (h : GGHasLabel (⟨.A, 1, k⟩ : LargeEvenLabel) R)
    (hsimple : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : 2 ≤ k := by
  unfold GGHasLabel at h
  unfold LargeEvenRawDatum at h
  dsimp only at h
  simp only [one_add_one_eq_two] at h
  unfold LargeEvenRecipeLinear at h
  obtain ⟨E, hfield, hfin, hE, h⟩ := h
  let : Field E := hfield
  let : Finite E := hfin
  by_contra hk
  push Not at hk
  interval_cases k
  · simp at hE
    have hsub : Subsingleton E := (Finite.card_le_one_iff_subsingleton).mp (by omega)
    exact zero_ne_one (Subsingleton.elim (0 : E) 1)
  · simp at hE
    obtain ⟨e⟩ := h
    have hSL : LargeEvenSLGroup (Fin 2) E = CFSG.Open.StatedSL 2 E :=
      @CFSG.Assembly.largeEvenSLGroup_eq_statedSL E hfield 2
    obtain ⟨e2⟩ := @CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
      2 E hfield (LargeEvenSLGroup (Fin 2) E) hSL
    have := @CFSG.LocalAnalysis.GLTheoremA.rtd_isSolvable_statedProj_two_of_card_two E hfield hfin hE
    have : Group.IsSolvable R :=
      Group.isSolvable_of_isSolvable_injective
        (f := (e.trans e2 : R →* CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 E)))
        (e.trans e2).injective
    have : IsSimpleGroup R := hsimple
    have : IsMulCommutative R := CFSG.OrderReductions.Helpers.simple_solvable_isMulCommutative R
    obtain ⟨a, b, hab⟩ := hna
    exact hab (mul_comm a b)

private theorem orthTAOne_iso {k : ℕ} {lab0 : LargeEvenLabel}
    (h : GGLabelIso (⟨.A, 1, k⟩ : LargeEvenLabel) lab0) :
    (lab0.tag = .A ∧ lab0.rank = 1) ∨ (lab0.tag = .twD ∧ lab0.rank = 2) := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · left; rw [← h]; exact ⟨rfl, rfl⟩
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · right; rw [h.1]; exact ⟨rfl, rfl⟩

private theorem orthTAOne_lambda2_A1 {k : ℕ} (hk : 2 ≤ k) :
    LargeEvenInLambda2 (⟨.A, 1, k⟩ : LargeEvenLabel) := by
  have h1 : 1 ≤ k := by omega
  exact ⟨h1, le_refl 1, fun _ => hk⟩

private theorem orthTAOne_lambda2_A {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hrn : r = 1 → 2 ≤ n) : LargeEvenInLambda2 (⟨.A, r, n⟩ : LargeEvenLabel) :=
  ⟨hn, hr, hrn⟩

private theorem orthTAOne_lambda2_twA {r n : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hrn : r = 2 → 2 ≤ n) : LargeEvenInLambda2 (⟨.twA, r, n⟩ : LargeEvenLabel) :=
  ⟨hn, hr, hrn⟩

private theorem orthTAOne_lambda2_D {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.D, r, n⟩ : LargeEvenLabel) :=
  ⟨hn, hr⟩

private theorem orthTAOne_lambda2_twD {r n : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.twD, r, n⟩ : LargeEvenLabel) :=
  ⟨hn, hr⟩

theorem orthT_A1
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {k : ℕ} (hlab : GGHasLabel ⟨.A, 1, k⟩ (J' ⧸ Subgroup.center J')) :
    Nat.card Ā ≤ 3 ^ 2 := by
  obtain ⟨x, Â, hδ', hx, hx1, hxÂ, hÂ, hcard, hconj, hker, hblock, hfixed, hdisj⟩ :=
    orthT_lift hQ hT hR hĀI
  have hq : CFSG.Assembly.IsQuasisimple J' := hR.comp.2.2
  obtain ⟨hsimple, hna⟩ := ggQuasisimple_centerQuot hq
  have hk2 : 2 ≤ k := orthTAOne_k hlab hsimple hna
  have hlamk : LargeEvenInLambda2 (⟨.A, 1, k⟩ : LargeEvenLabel) := orthTAOne_lambda2_A1 hk2
  have hn1 : 1 ≤ n := by
    have h2 : 2 ≤ Nat.card K := by
      by_contra h
      have hle : Nat.card K ≤ 1 := by omega
      have hsub : Subsingleton K := (Finite.card_le_one_iff_subsingleton).mp hle
      obtain ⟨a, b, hab⟩ := exists_pair_ne K
      exact hab (Subsingleton.elim a b)
    rw [hK] at h2
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    norm_num at h2
  rcases hdisj with ⟨h, hh, hne1, hqh, hJeq⟩ | ⟨F, hFq, hFle, hFn, hJeq⟩
  ·
    obtain ⟨hm, -, hcases⟩ :=
      orthT_blockLabel hK hx hh hne1 hqh (L := J') hJeq
    have hm_eq : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 2 := by
      rcases hcases with ⟨hne, h3n, hlab0⟩ | ⟨hself, h3n, hsub⟩
      ·
        have hn2 : 2 ≤ n := by
          have : n ≠ 1 := by
            intro hn1'
            subst hn1'
            norm_num at h3n
          omega
        have hlam0 : LargeEvenInLambda2
            (⟨.A, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
          orthTAOne_lambda2_A (by omega) hn1 (fun _ => hn2)
        have hiso := orthTAOne_iso (ggLabelRigidInput_holds (⟨.A, 1, k⟩ : LargeEvenLabel)
          (⟨.A, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
          (J' ⧸ Subgroup.center J') hlamk hlam0 hlab hlab0)
        rcases hiso with ⟨-, hr⟩ | ⟨ht, -⟩
        · have h1 : 1 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by omega
          rw [Nat.sub_eq_iff_eq_add h1] at hr
          simpa using hr
        · exact absurd ht (by simp)
      · rcases hsub with ⟨hm2, hn2, hlab0⟩ | ⟨hm3, hne, hlab0⟩
        · exact hm2
        ·
          exfalso
          have hlam0 : LargeEvenInLambda2
              (⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) := by
            refine orthTAOne_lambda2_twA (by omega) hn1 ?_
            intro hh'
            have : n ≠ 1 := by
              intro hn1'
              exact hne ⟨hn1', by omega⟩
            omega
          have hlab0' : GGHasLabel
              (⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
              (J' ⧸ Subgroup.center J') := hlab0
          have hiso := orthTAOne_iso (ggLabelRigidInput_holds (⟨.A, 1, k⟩ : LargeEvenLabel)
            (⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
            (J' ⧸ Subgroup.center J') hlamk hlam0 hlab hlab0')
          rcases hiso with ⟨ht, -⟩ | ⟨ht, -⟩ <;> exact absurd ht (by simp)
    have hJle : J' ≤ componentImage Q (x : V ≃ₗ[K] V) h := le_of_eq hJeq
    have hbound := orthT_rankA1 hx hx1 hÂ hxÂ
      (Or.inl ⟨h, hh, hne1, hm_eq, hJle⟩) hker
    rw [← hcard]
    exact hbound
  ·
    obtain ⟨s, hdim, hcases⟩ :=
      orthT_fixedLabel hK hQ hx hFq hFle hFn (L := J') hJeq
    rcases hcases with
      ⟨hs4, hplus, hlab0⟩ | ⟨hs4, hminus, hlab0⟩ | ⟨hs3, hplus, hlab0⟩ |
      ⟨hs3, hminus, hlab0⟩ | ⟨hs2, hminus, hlab0⟩ | ⟨hs2, hplus, hn2, hlab0⟩
    ·
      exfalso
      have hlam0 : LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) :=
        orthTAOne_lambda2_D (by omega) hn1
      have hlab0' : GGHasLabel (⟨.D, s, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') := hlab0
      have hiso := orthTAOne_iso (ggLabelRigidInput_holds (⟨.A, 1, k⟩ : LargeEvenLabel)
        (⟨.D, s, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') hlamk hlam0 hlab hlab0')
      rcases hiso with ⟨ht, -⟩ | ⟨ht, -⟩ <;> exact absurd ht (by simp)
    ·
      exfalso
      have hlam0 : LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) :=
        orthTAOne_lambda2_twD (by omega) hn1
      have hlab0' : GGHasLabel (⟨.twD, s, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') := hlab0
      have hiso := orthTAOne_iso (ggLabelRigidInput_holds (⟨.A, 1, k⟩ : LargeEvenLabel)
        (⟨.twD, s, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') hlamk hlam0 hlab hlab0')
      rcases hiso with ⟨ht, -⟩ | ⟨ht, hr⟩
      · exact absurd ht (by simp)
      · have hr' : s = 2 := hr
        omega
    ·
      exfalso
      have hlam0 : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) :=
        orthTAOne_lambda2_A (by omega) hn1 (by omega)
      have hlab0' : GGHasLabel (⟨.A, 3, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') := hlab0
      have hiso := orthTAOne_iso (ggLabelRigidInput_holds (⟨.A, 1, k⟩ : LargeEvenLabel)
        (⟨.A, 3, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') hlamk hlam0 hlab hlab0')
      rcases hiso with ⟨-, hr⟩ | ⟨ht, -⟩
      · have hr' : (3 : ℕ) = 1 := hr
        omega
      · exact absurd ht (by simp)
    ·
      exfalso
      have hlam0 : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
        orthTAOne_lambda2_twA (by omega) hn1 (by omega)
      have hlab0' : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') := hlab0
      have hiso := orthTAOne_iso (ggLabelRigidInput_holds (⟨.A, 1, k⟩ : LargeEvenLabel)
        (⟨.twA, 3, n⟩ : LargeEvenLabel) (J' ⧸ Subgroup.center J') hlamk hlam0 hlab hlab0')
      rcases hiso with ⟨ht, -⟩ | ⟨ht, -⟩ <;> exact absurd ht (by simp)
    ·
      have h4 : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 := by rw [hdim, hs2]
      have hJle : J' ≤ fixedComponentImage Q (x : V ≃ₗ[K] V) := by
        rw [hJeq]
        refine Subgroup.map_mono ?_
        intro g hg
        exact Subgroup.mem_subgroupOf.mpr (hFle (Subgroup.mem_subgroupOf.mp hg))
      have hbound := orthT_rankA1 hx hx1 hÂ hxÂ (Or.inr ⟨h4, hminus, hJle⟩) hker
      rw [← hcard]
      exact hbound
    ·
      exfalso
      have h4le : 4 ≤ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) := by rw [hdim, hs2]
      have h4eq : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 := by rw [hdim, hs2]
      have hsmall : ¬ (Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
          CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          n = 1) := by
        rintro ⟨-, -, hn1'⟩
        omega
      obtain ⟨F₀, hF₀q, hF₀le, hF₀n, hF₀'⟩ := orthT_fixedExists hK hQ hx h4le hsmall
      obtain ⟨F₁, hF₁q, hF₁le, hF₁n, hne⟩ := hF₀' h4eq hplus
      exact hne ((hfixed F₁ hF₁q hF₁le hF₁n).trans (hfixed F₀ hF₀q hF₀le hF₀n).symm)

end OrthAux

end CFSG.StandardType.TablePThreeKG

end
