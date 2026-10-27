module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueezeDefs
import CFSG.RankThree.PartOne.S11d.OrthLayer
import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
import CFSG.RankThree.PartOne.S15K.OrthModel
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgInner
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCPrimary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7DDFBAux_D_tag_ne {tag : LargeEvenLieTag}
    (h : tag = .D ∨ tag = .twD) : tag ≠ .A ∧ tag ≠ .twA ∧ tag ≠ .B ∧ tag ≠ .C := by
  rcases h with rfl | rfl <;> decide

private theorem hdRo7DDFBAux_ggLabelIso_D {tag tag' : LargeEvenLieTag} {r r' n n' : ℕ}
    (h1 : tag = .D ∨ tag = .twD) (h2 : tag' = .D ∨ tag' = .twD)
    (h : GGLabelIso ⟨tag, r, n⟩ ⟨tag', r', n'⟩) : tag = tag' ∧ r = r' ∧ n = n' := by
  have hne := hdRo7DDFBAux_D_tag_ne h1
  have hne' := hdRo7DDFBAux_D_tag_ne h2
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨by simpa using congrArg LargeEvenLabel.tag h,
      by simpa using congrArg LargeEvenLabel.rank h,
      by simpa using congrArg LargeEvenLabel.n h⟩
  · have hB : tag = .B ∨ tag = .C := by simpa using h.1
    rcases hB with hB | hB
    · exact absurd hB (by rcases h1 with rfl | rfl <;> decide)
    · exact absurd hB (by rcases h1 with rfl | rfl <;> decide)
  · have ht : tag' = .A := by simpa using congrArg LargeEvenLabel.tag h.2
    exact absurd ht hne'.1
  · have ht : tag = .A := by simpa using congrArg LargeEvenLabel.tag h.1
    exact absurd ht hne.1
  · have ht : tag' = .twA := by simpa using congrArg LargeEvenLabel.tag h.2
    exact absurd ht hne'.2.1
  · have ht : tag = .twA := by simpa using congrArg LargeEvenLabel.tag h.1
    exact absurd ht hne.2.1
  · have ht : tag' = .A := by simpa using congrArg LargeEvenLabel.tag h.2
    exact absurd ht hne'.1
  · have ht : tag = .A := by simpa using congrArg LargeEvenLabel.tag h.2
    exact absurd ht hne.1

private theorem hdRo7DDFBAux_not_ggLabelIso_D_small {tag tag' : LargeEvenLieTag} {r n r' n' : ℕ}
    (h1 : tag = .D ∨ tag = .twD) (hr : 4 ≤ r) (h2 : tag' = .A ∨ tag' = .twA) :
    ¬ GGLabelIso ⟨tag, r, n⟩ ⟨tag', r', n'⟩ := by
  have hne := hdRo7DDFBAux_D_tag_ne h1
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · have ht : tag = tag' := by simpa using congrArg LargeEvenLabel.tag h
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
      exact absurd ht (by decide)
  · have hB : tag = .B ∨ tag = .C := by simpa using h.1
    rcases hB with hB | hB
    · exact absurd hB (by rcases h1 with rfl | rfl <;> decide)
    · exact absurd hB (by rcases h1 with rfl | rfl <;> decide)
  · have h3 : r = 3 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : tag = .A := by simpa using congrArg LargeEvenLabel.tag h.1
    exact absurd ht hne.1
  · have h3 : r = 3 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : tag = .twA := by simpa using congrArg LargeEvenLabel.tag h.1
    exact absurd ht hne.2.1
  · have h3 : r = 2 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : tag = .A := by simpa using congrArg LargeEvenLabel.tag h.2
    exact absurd ht hne.1

private theorem hdRo7DDFBAux_not_ggLabelIso_D_twA {tag : LargeEvenLieTag} {r n r' n' : ℕ}
    (h1 : tag = .D ∨ tag = .twD) (hr : 4 ≤ r) :
    ¬ GGLabelIso ⟨tag, r, n⟩ ⟨.twA, r', n'⟩ := by
  have hne := hdRo7DDFBAux_D_tag_ne h1
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · have ht : tag = .twA := by simpa using congrArg LargeEvenLabel.tag h
    exact hne.2.1 ht
  · have hB : tag = .B ∨ tag = .C := by simpa using h.1
    rcases hB with hB | hB
    · exact absurd hB (by rcases h1 with rfl | rfl <;> decide)
    · exact absurd hB (by rcases h1 with rfl | rfl <;> decide)
  · have h3 : r = 3 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : tag = .A := by simpa using congrArg LargeEvenLabel.tag h.1
    exact hne.1 ht
  · have h3 : r = 3 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : tag = .twA := by simpa using congrArg LargeEvenLabel.tag h.1
    exact hne.2.1 ht
  · have h3 : r = 2 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : (.twA : LargeEvenLieTag) = .twD := by
      simpa using congrArg LargeEvenLabel.tag h.1
    exact absurd ht (by decide)

private theorem hdRo7DDFBAux_sub_mem_others {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q p x) (v : V) :
    x v - v ∈ CFSG.RankThree.PartOne.KCOrthogonal.othersSpace x.toLinearMap
      (Polynomial.X - 1) := by
  obtain ⟨hc, -⟩ := hx.fixed_others
  obtain ⟨w, hw, r, hr, rfl⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_add_of_isCompl hc v
  have hxw : x w = w := CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace.mp hw
  have hxr : x r ∈ CFSG.RankThree.PartOne.KCOrthogonal.othersSpace x.toLinearMap
      (Polynomial.X - 1) :=
    CFSG.RankThree.PartOne.KCOrthogonal.mem_othersSpace_of_apply
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hr
  have : x (w + r) - (w + r) = x r - r := by rw [map_add, hxw]; abel
  rw [this]
  exact Submodule.sub_mem _ hxr hr

private theorem hdRo7DDFBAux_lam2_D {s : ℕ} (h : 3 ≤ s) :
    LargeEvenInLambda2 ⟨.D, s, 1⟩ :=
  ⟨le_rfl, h⟩

private theorem hdRo7DDFBAux_lam2_twD {s : ℕ} (h : 2 ≤ s) :
    LargeEvenInLambda2 ⟨.twD, s, 1⟩ :=
  ⟨le_rfl, h⟩

private theorem hdRo7DDFBAux_lam2_A3 : LargeEvenInLambda2 ⟨.A, 3, 1⟩ := by
  simp [LargeEvenInLambda2]

private theorem hdRo7DDFBAux_lam2_twA3 : LargeEvenInLambda2 ⟨.twA, 3, 1⟩ := by
  simp [LargeEvenInLambda2]

private theorem hdRo7DDFBAux_lam2_A12 : LargeEvenInLambda2 ⟨.A, 1, 2⟩ := by
  simp [LargeEvenInLambda2]

private theorem hdRo7DDFBAux_lam2_twA {k : ℕ} (h : 4 ≤ k) :
    LargeEvenInLambda2 ⟨.twA, k - 1, 1⟩ := by
  refine ⟨le_rfl, ?_, ?_⟩
  · show 2 ≤ k - 1
    omega
  · show k - 1 = 2 → 2 ≤ 1
    omega

theorem d_fixBlock_holds : DFixBlockLeaf := by
  intro hRig F hFld hFin hChar hFcard V hVadd hVmod hVfd Q hQ ℓ hdim hℓ t ht C hC hlab
  obtain ⟨lab, hΛ, hlabC, htagD, hn1, hrank⟩ := hlab
  have : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
  have hx : OddOrderIsometry Q 3 (t : V ≃ₗ[F] V) :=
    CFSG.StandardType.OmNsRootGen.oddOrderIsometry_of_orthDerived_pow_eq_one hQ
      (by norm_num) (by norm_num) ht
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q := CFSG.RankThree.PartOne.piOrth Q
  have hinj : Function.Injective ρ :=
    CFSG.RankThree.PartOne.S15K.mk_injective_orth hQ
  let J' : Subgroup (ProjOrthDerived Q) := C.map ρ
  have hJ' : CFSG.Open.IsComponentOf J' (centralizerImage Q (t : V ≃ₗ[F] V)) := by
    have hmap : (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))).map ρ
        = centralizerImage Q (t : V ≃ₗ[F] V) :=
      CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage t
    rw [← hmap]
    exact isComponentOf_map_mulEquiv
      (MulEquiv.ofBijective ρ ⟨hinj, QuotientGroup.mk'_surjective _⟩)
      (isComponentOf_iff_open.mp hC)
  have hlabJ' : GGHasLabel lab (↥J' ⧸ Subgroup.center ↥J') :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.equivMapOfInjective C ρ hinj) hlabC
  have hr2 : lab.rank = ℓ - 2 := by omega
  have hr4 : 4 ≤ lab.rank := by omega
  have hT : ∃ U : Submodule F V, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ (m := ℓ) (by omega) hdim
  rcases CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_component_dichotomy
      (p := 3) (by norm_num) (by norm_num) hQ hT
      (by rw [ringChar.eq F 2]; norm_num) hx J' hJ'
    with ⟨h, hh, hne1, hq, hJeq⟩ | ⟨-, F₀, hFq, hFle, hFn, hJeq⟩
  ·
    obtain ⟨-, -, hmain⟩ := TablePThreeKG.orthT_blockLabel (K := F) (n := 1)
      (by rw [hFcard]; norm_num) hx hh hne1 hq hJeq
    rcases hmain with ⟨-, h3, -⟩ | ⟨-, h3, hrest⟩
    · omega
    · rcases hrest with ⟨-, hn2, -⟩ | ⟨hm3, hnot, htwA⟩
      · omega
      · have hm4 : 4 ≤ primaryMultiplicity (t : V ≃ₗ[F] V).toLinearMap h := by omega
        exact absurd
          (hRig lab ⟨.twA, primaryMultiplicity (t : V ≃ₗ[F] V).toLinearMap h - 1, 1⟩ _
            hΛ (hdRo7DDFBAux_lam2_twA hm4) hlabJ' htwA)
          (hdRo7DDFBAux_not_ggLabelIso_D_twA htagD hr4)
  ·
    obtain ⟨s, hs, hcases⟩ := TablePThreeKG.orthT_fixedLabel (K := F) (n := 1)
      (by rw [hFcard]; norm_num) hQ hx hFq hFle hFn hJeq
    have hCeq : C = F₀.subgroupOf (orthDerived Q) := Subgroup.map_injective hinj hJeq
    have hseq : s = ℓ - 2 := by
      rcases hcases with ⟨h4, -, hD⟩ | ⟨h4, -, hD⟩ | ⟨h3, -, hA⟩ | ⟨h3, -, hA⟩ |
        ⟨h2, -, hA⟩ | ⟨h2, -, hn2, hA⟩
      · have hr := (hdRo7DDFBAux_ggLabelIso_D htagD (Or.inl rfl)
          (hRig lab ⟨.D, s, 1⟩ _ hΛ (hdRo7DDFBAux_lam2_D (by omega)) hlabJ' hD)).2.1
        omega
      · have hr := (hdRo7DDFBAux_ggLabelIso_D htagD (Or.inr rfl)
          (hRig lab ⟨.twD, s, 1⟩ _ hΛ (hdRo7DDFBAux_lam2_twD (by omega)) hlabJ' hD)).2.1
        omega
      · exact absurd (hRig lab ⟨.A, 3, 1⟩ _ hΛ hdRo7DDFBAux_lam2_A3 hlabJ' hA)
          (hdRo7DDFBAux_not_ggLabelIso_D_small htagD hr4 (Or.inl rfl))
      · exact absurd (hRig lab ⟨.twA, 3, 1⟩ _ hΛ hdRo7DDFBAux_lam2_twA3 hlabJ' hA)
          (hdRo7DDFBAux_not_ggLabelIso_D_small htagD hr4 (Or.inr rfl))
      · exact absurd (hRig lab ⟨.A, 1, 2⟩ _ hΛ hdRo7DDFBAux_lam2_A12 hlabJ' hA)
          (hdRo7DDFBAux_not_ggLabelIso_D_small htagD hr4 (Or.inl rfl))
      · omega
    refine ⟨?_, ?_⟩
    · change Module.finrank F ↥(fixedSpace (t : V ≃ₗ[F] V)) = 2 * (ℓ - 2)
      rw [hs, hseq]
    · intro c hc v
      have hmem : ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ F₀ :=
        Subgroup.mem_subgroupOf.mp (hCeq.le hc)
      have hcB : ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
          supportedBlock Q (t : V ≃ₗ[F] V) (Polynomial.X - 1) :=
        supportedFixedDerived_le_supportedBlock (hFle hmem)
      exact (mem_supportedBlock.mp hcB).2 _ (hdRo7DDFBAux_sub_mem_others hx v)

end CFSG.StandardType.HdRo7D
