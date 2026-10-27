module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphPlus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinusHolds
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

namespace NoOffOm

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Glue

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {G : Type} [Group G] [Finite G] {U : Type} [Group U]

omit [Finite G] in
theorem exists_monoFrame_of_spinModel (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (ψ : U →* G) (hψ : Function.Injective ψ) (π : U →* matrixDerived Q)
    (hπ : Function.Bijective π) (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hAut : ∀ α : MulAut (matrixDerived Q), α ^ p = 1 →
      ∃ g' : similarityPairs Q, CFSG.RankThree.PartOne.AUTSL.conjAct Q g' = α) :
    ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G), Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → NoOffUO.GGMonoAct ι g := by
  classical
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : matrixDerived Q →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨πe u, by simp [hφ]⟩
  have hBφ : Bs ≤ φ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := hdiag b hb
    rw [hC, Subgroup.mem_bot] at hbg
    rw [hφrange, eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  refine exists_monoFrame_of_orthModel hnd hT hp hp2 hBs hSC φ hφinj hBφ ?_
  intro g hgN hgB hgp
  have hgN' : g ∈ Subgroup.normalizer (φ.range : Set G) := by rw [hφrange]; exact hgN
  have hmem : ∀ X : matrixDerived Q, ∃ Y : matrixDerived Q, φ Y = g⁻¹ * φ X * g := by
    intro X
    obtain ⟨Y, hY⟩ := inv_mul_mul_mem hgN' (MonoidHom.mem_range.mpr ⟨X, rfl⟩)
    exact ⟨Y, hY⟩
  choose α₀ hα₀ using hmem
  have hα₀mul : ∀ X Y, α₀ (X * Y) = α₀ X * α₀ Y := fun X Y => hφinj (by
    rw [hα₀, map_mul, map_mul, hα₀, hα₀]
    group)
  have hα₀inj : Function.Injective α₀ := fun X Y hXY => hφinj (by
    have h1 := hα₀ X
    rw [hXY, hα₀] at h1
    calc φ X = g * (g⁻¹ * φ X * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * φ Y * g) * g⁻¹ := by rw [h1]
      _ = φ Y := by group)
  have : Finite (matrixDerived Q) := inferInstance
  set α : MulAut (matrixDerived Q) :=
    MulEquiv.ofBijective (MonoidHom.mk' α₀ hα₀mul)
      (Finite.injective_iff_bijective.mp hα₀inj) with hαdef
  have hα : ∀ X, φ (α X) = g⁻¹ * φ X * g := fun X => hα₀ X
  have hαpow : ∀ (k : ℕ) X, φ ((α ^ k) X) = (g ^ k)⁻¹ * φ X * g ^ k := by
    intro k
    induction k with
    | zero => intro X; simp
    | succ k ih =>
      intro X
      rw [pow_succ', MulAut.mul_apply, hα, ih, pow_succ']
      group
  have hαp : α ^ p = 1 := MulEquiv.ext fun X => hφinj (by
    rw [hαpow, hgp, inv_one, one_mul, mul_one, MulAut.one_apply])
  obtain ⟨g', hg'⟩ := hAut α hαp
  exact ⟨g', fun X => by rw [hg', hα]⟩

end Glue

end NoOffOm

section Tags

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem ggSixBstarMonoFrameOn_POmegaPlusNotD4Three :
    GGSixBstarMonoFrameOn GGPOmegaPlusNotD4Three := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hne⟩ := hP
  revert ψ
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hctx hC
    have hn4 : 4 ≤ n := hctx.2.2.2.1.1.2.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
    have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
    obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
        ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
      exact hker
    have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact hC
    obtain ⟨hnd, hT⟩ :=
      CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus n
        (GaloisField 2 f) hn
    have hAut : ∀ α : MulAut (matrixDerived (coordinateQuadPlus n (GaloisField 2 f))),
        α ^ p = 1 → ∃ g' : similarityPairs (coordinateQuadPlus n (GaloisField 2 f)),
          CFSG.RankThree.PartOne.AUTSL.conjAct _ g' = α := by
      intro α hα
      obtain ⟨h, τ, rfl⟩ := OrdPGraphOmega.exists_conj_mul_fieldAutP_of_pow hn4 hp hp2 hne hα
      have e1 : MulAut.conj h = CFSG.RankThree.PartOne.AUTSL.conjAct _
          (matrixIsometryInclusion _ ⟨h.val, matrixDerived_le_isometries _ h.2⟩) :=
        (CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_of_mem ⟨h.val, _⟩ h.2).symm
      rw [e1, AutOm.fieldAutP_apply, ← map_mul]
      exact ⟨_, rfl⟩
    obtain ⟨r, ι, hinj, hrangeι, hmono⟩ := NoOffOm.exists_monoFrame_of_spinModel hnd hT hp hp2
      hctx.2.1.2.1 hctx.2.1.2.2.2 ψ hψinj (AutOm.spinModelPlus hn)
      ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ hCψ
      (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
      hAut
    refine ⟨r, ι, hinj, hrangeι, fun g hgM hgB hgp => hmono g ?_ hgB hgp⟩
    rw [hrange]
    exact hgM
  · intro ψ hctx
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

theorem ggSixBstarMonoFrameOn_POmegaMinusLabel : GGSixBstarMonoFrameOn GGPOmegaMinusLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  subst hP
  revert ψ
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  intro ψ hctx hC
  have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hirr := minusCoeffs_irr 2 f
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  obtain ⟨hnd, hT⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus n
      (GaloisField 2 f) _ _ hn hirr
  have hAut : ∀ α : MulAut (matrixDerived (coordinateQuadMinus n (GaloisField 2 f) (by omega)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)), α ^ p = 1 →
      ∃ g' : similarityPairs (coordinateQuadMinus n (GaloisField 2 f) (by omega)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        CFSG.RankThree.PartOne.AUTSL.conjAct _ g' = α := fun α _ =>
    CFSG.RankThree.PartOne.AUTSL.exists_pair_of_aut
      ⟨_, AutOm.tailVec_form_ne_zero n (by omega) _ _⟩
      (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus
        (GaloisField 2 f) n hn _ _ hirr) α
  obtain ⟨r, ι, hinj, hrangeι, hmono⟩ := NoOffOm.exists_monoFrame_of_spinModel hnd hT hp hp2
    hctx.2.1.2.1 hctx.2.1.2.2.2 ψ hψinj (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ hCψ
    (fun b hb => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
    hAut
  refine ⟨r, ι, hinj, hrangeι, fun g hgM hgB hgp => hmono g ?_ hgB hgp⟩
  rw [hrange]
  exact hgM

theorem ggSixBstarNoOffenderAt_POmegaMinus : GGSixBstarNoOffenderAt .POmegaMinus :=
  ggSixBstarNoOffenderAt_POmegaMinus_of_frame ggSixBstarMonoFrameOn_POmegaMinusLabel

theorem ggSixBstarNoOffenderOn_POmegaPlusNotD4Three :
    GGSixBstarNoOffenderOn GGPOmegaPlusNotD4Three :=
  ggNoOffender_of_monoFrameOn ggSixBstarMonoFrameOn_POmegaPlusNotD4Three

theorem ggSixBstarNoOffenderAt_POmegaPlus_of_D4 (hD4 : GGSixBstarNoOffenderOn GGPOmegaPlusD4Three) :
    GGSixBstarNoOffenderAt .POmegaPlus :=
  ggSixBstarNoOffenderAt_POmegaPlus_of_frame ggSixBstarMonoFrameOn_POmegaPlusNotD4Three hD4

end Tags

end CFSG.StandardType
