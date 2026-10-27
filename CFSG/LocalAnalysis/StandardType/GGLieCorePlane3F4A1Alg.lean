module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Orbit
public import CFSG.LocalAnalysis.StandardType.GGFamTypeAFrames
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA1Part1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A1SelectedPair
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4A1_fixedGroup_alg
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {D : LangDatum Tag.F4 Ω}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Ωˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 1 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 2)
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i) :
    GGLieSL2Model ↥(rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  let χ := jointChar a₁ a₂
  let Ψ := componentRoots χ i
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨γ, hγr, hΨpair⟩ :=
    CFSG.StandardType.TableCRes.fam_exists_pair_of_rank_one (χ := χ) i hshape.2
  have hΨp : Ψ = {γ, -γ} := hΨpair
  have hγmem : γ ∈ Ψ := by rw [hΨp]; simp
  have hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ := by
    intro α hα
    have hcomp := ggLieF4Plane_image_eq h (⟦⟨α, hα⟩⟧ : KernelComponent χ)
    have hmem : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
    have hρα : ρ α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := by
      rw [← hcomp]
      exact ⟨α, hmem, rfl⟩
    exact hρα.1
  have hinner : twistInner Ψ ρ := by
    have hργ : ρ γ ∈ Ψ := by
      have h' : ρ γ ∈ (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' Ψ :=
        ⟨γ, hγmem, rfl⟩
      have h'' : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' Ψ = Ψ := hρΨ
      rw [h''] at h'
      exact h'
    have hργ' : ρ γ = γ ∨ ρ γ = -γ := by
      have h := hργ
      rw [hΨp] at h
      simpa using h
    have hδ' : ∀ {δ : Fin Tag.F4.rank → ℤ}, δ ∈ Ψ → δ = γ ∨ δ = -γ := by
      intro δ hδ
      have h := hδ
      rw [hΨp] at h
      simpa using h
    rcases hργ' with hργ_eq | hργ_neg
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      intro δ hδ
      rcases hδ' hδ with rfl | rfl
      · simpa using hργ_eq
      · simp [h.frob.neg_eq, hργ_eq]
    · refine ⟨rootReflection γ, Subgroup.subset_closure ⟨γ, hγmem, rfl⟩, ?_⟩
      intro δ hδ
      rcases hδ' hδ with rfl | rfl
      · simp [hργ_neg, CFSG.HardMathSupport.Timmesfeld.LangTorus.rootReflection_smul_self hγr]
      · simp [h.frob.neg_eq, hργ_neg, smul_neg,
          CFSG.HardMathSupport.Timmesfeld.LangTorus.rootReflection_smul_self hγr]
  have hcomp : (rootSL2 Tag.F4 Ω γ).range = rootSpan Tag.F4 Ω Ψ := by
    rw [hΨp, CFSG.LieType.HighestRoot.rootSpan_pair_eq γ]
    exact CFSG.StandardType.F4ExplicitPos.RationalA1.rootSL2_range_eq_sup hγr
  let K : Subfield Ω := RingHom.eqLocusField (iterateFrobenius Ω 2 f) (RingHom.id Ω)
  have hKset : (K : Set Ω) = {c : Ω | c ^ (2 ^ f) = c} := by
    ext c
    change c ∈ RingHom.eqLocusField (iterateFrobenius Ω 2 f) (RingHom.id Ω) ↔ _
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
    rfl
  have hKfin : (K : Set Ω).Finite := by
    rw [hKset]
    exact (ncard_pow_eq_self 2 f (by omega)).1
  have hKcard : Nat.card ↥K = 2 ^ f := by
    have h1 : Nat.card ↥K = (K : Set Ω).ncard := Nat.card_coe_set_eq (K : Set Ω)
    rw [h1, hKset]
    exact (ncard_pow_eq_self 2 f (by omega)).2
  have : Finite K := hKfin.to_subtype
  obtain ⟨σ, z, hσc, _hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      D f hf hqf ρ h.frob i hker hinner
  have hσ : ∀ c, σ c = c ^ Nat.card K := fun c => by rw [hσc c, hqf, ← hKcard]
  have hzH : ∀ g, g ∈ (rootSL2 Tag.F4 Ω γ).range ↔
      z * g * z⁻¹ ∈ (rootSL2 Tag.F4 Ω γ).range := by
    intro g
    rw [hcomp]
    exact CFSG.StandardType.F4ExplicitPos.NativePinFinal.normalizesAll_apply hnorm i g
  have hzF : ∀ g ∈ (rootSL2 Tag.F4 Ω γ).range,
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    rw [hcomp] at hg
    exact hgoal g hg
  have hNdef :
      (CFSG.StandardType.F4ExplicitPos.RationalA1.phiA1 (k := K) z γ).range =
        rootSpan Tag.F4 Ω Ψ ⊓ D.model := by
    rw [CFSG.StandardType.F4ExplicitPos.RationalA1.phiA1_range_of_normalizes
      (k := K) D σ hσ z γ hγr hzH hzF, hcomp]
  let e1 :
      Matrix.SpecialLinearGroup (Fin 2) K ≃*
        ↥(CFSG.StandardType.F4ExplicitPos.RationalA1.phiA1 (k := K) z γ).range :=
    MonoidHom.ofInjective
      (CFSG.StandardType.F4ExplicitPos.RationalA1.phiA1_injective (Ω := Ω) (k := K) z γ)
  let e2 : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(CFSG.Open.StatedSL 2 K) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  refine ⟨K, inferInstance, inferInstance, hKcard, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hNdef.symm).trans (e1.symm.trans e2)

end CFSG.StandardType.LieCore
