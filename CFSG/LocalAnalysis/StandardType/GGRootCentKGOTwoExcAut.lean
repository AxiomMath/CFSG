module

public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.KGExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem exists_conj_entrywise_of_mem_normalizer
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {G : Type*} [Group G]
    {ψ : adjointGroup τ K →* G} (hψ : Function.Injective ψ) {a : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (g : adjointGroup τ K) (σ : K ≃+* K), ∀ k : adjointGroup τ K,
      a * ψ k * a⁻¹ = ψ (g * entrywiseAdjointAut τ σ k * g⁻¹) := by
  classical
  let Θ : adjointGroup τ K ≃* ψ.range := MonoidHom.ofInjective hψ
  let c : MulAut ψ.range := conjAut ψ.range ha
  let α : MulAut (adjointGroup τ K) := (Θ.trans c).trans Θ.symm
  obtain ⟨⟨g, σ⟩, hg, -⟩ :=
    (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ).1 α
  have hα : ∀ h : adjointGroup τ K, α h = g * entrywiseAdjointAut τ σ h * g⁻¹ := fun h =>
    Subtype.ext (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut] using hg h)
  have hΘ : ∀ x : adjointGroup τ K, Θ x = ⟨ψ x, ⟨x, rfl⟩⟩ := fun x =>
    Subtype.ext (MonoidHom.ofInjective_apply hψ)
  refine ⟨g, σ, fun k => ?_⟩
  have hmem : a * ψ k * a⁻¹ ∈ ψ.range :=
    (Subgroup.mem_normalizer_iff.mp ha (ψ k)).mp ⟨k, rfl⟩
  have h1 : Θ (α k) = ⟨a * ψ k * a⁻¹, hmem⟩ := by
    change Θ (Θ.symm (c (Θ k))) = _
    rw [hΘ k, MulEquiv.apply_symm_apply]
    exact Subtype.ext (coe_conjAut ha ⟨ψ k, ⟨k, rfl⟩⟩)
  have h2 : Θ (α k) = ⟨ψ (g * entrywiseAdjointAut τ σ k * g⁻¹), ⟨_, rfl⟩⟩ := by
    rw [hα]
    simp only [map_mul, map_inv, hΘ]
  exact congrArg Subtype.val (h1.symm.trans h2)

end CFSG.StandardType.KGExc
