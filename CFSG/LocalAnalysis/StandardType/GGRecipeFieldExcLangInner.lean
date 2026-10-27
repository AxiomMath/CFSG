module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


@[expose] def InnerFieldTrivial (τ : Tag) (K : Type) [Field K] : Prop :=
  ∀ (ρ : K ≃+* K) (v : ModGL τ K), v ∈ inndiagGroup τ K →
    (∀ h ∈ adjointGroup τ K, Units.map (entrywiseHom ρ.toRingHom) h = v * h * v⁻¹) → ρ = 1

variable {τ : Tag} {K : Type} [Field K]

theorem innerFieldTrivial_of_hom (hΓ : ∀ b : Fin τ.rank → Kˣ, rootDiagUnit τ b ∈ adjointGroup τ K)
    (Θ : MulAut (adjointGroup τ K) →* (K ≃+* K))
    (hΘ : ∀ ρ : K ≃+* K, Θ (entrywiseAdjointAut τ ρ) = ρ)
    (hinn : ∀ x : adjointGroup τ K, Θ (MulAut.conj x) = 1) : InnerFieldTrivial τ K := by
  intro ρ v hv hρ
  have hvC : v ∈ adjointGroup τ K := by
    obtain ⟨b, j, hj, rfl⟩ := hv
    exact mul_mem (hΓ b) hj
  have hα : entrywiseAdjointAut τ ρ = MulAut.conj ⟨v, hvC⟩ :=
    MulEquiv.ext fun h => Subtype.ext (by rw [coe_entrywiseAdjointAut, hρ h h.2]; rfl)
  rw [← hΘ ρ, hα, hinn]

theorem rootDiagUnit_mem_adjointGroup_of_det_one (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8)
    (b : Fin τ.rank → Kˣ) : rootDiagUnit τ b ∈ adjointGroup τ K := by
  have hdet : τ.cartan.transpose.det = 1 := by
    rw [Matrix.det_transpose]
    rcases hτ with rfl | rfl | rfl
    · exact det_cartan_G2
    · exact det_cartan_F4
    · exact det_cartan_E8
  have hle : torusGroup τ K ≤ adjointGroup τ K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (u := b) fun i => by rw [hdet, zpow_one]]
  exact hle (list_prod_torusElt_mem_torusGroup _)

theorem hom_entrywiseAdjointAut_eq (Θ : MulAut (adjointGroup τ K) →* (K ≃+* K))
    (hΘ : ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) → Θ α = σ)
    (ρ : K ≃+* K) : Θ (entrywiseAdjointAut τ ρ) = ρ :=
  hΘ _ 1 ρ fun h => by rw [coe_entrywiseAdjointAut]; simp

theorem hom_conj_eq_one {Q : Type*} [Group Q] (Θ : MulAut (adjointGroup τ K) →* Q)
    (hker : Θ.ker = (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (x : adjointGroup τ K) : Θ (MulAut.conj x) = 1 := by
  rw [← MonoidHom.mem_ker, hker]
  exact ⟨x, rfl⟩

theorem innerFieldTrivial_E7_E8 {f : ℕ} (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = 2 ^ f)
    (hτ : τ = .E7 ∨ τ = .E8) : InnerFieldTrivial τ K := by
  have : CharP K 2 := charP_two_of_card hK
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  exact innerFieldTrivial_of_hom (rootDiagUnit_mem_adjointGroup_E7_E8 hτ (ringChar.eq K 2)) Θ
    (hom_entrywiseAdjointAut_eq Θ hΘ) (hom_conj_eq_one Θ hker)

theorem innerFieldTrivial_G2 {f : ℕ} (hf : 2 ≤ f) [Finite K] (hK : Nat.card K = 2 ^ f) :
    InnerFieldTrivial .G2 K := by
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  exact innerFieldTrivial_of_hom (rootDiagUnit_mem_adjointGroup_of_det_one (Or.inl rfl)) Θ
    (hom_entrywiseAdjointAut_eq Θ hΘ) (hom_conj_eq_one Θ hker)

theorem innerFieldTrivial_F4 {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = 2 ^ f) : InnerFieldTrivial .F4 K := by
  intro ρ v hv hρ
  have hvC : v ∈ adjointGroup .F4 K := by
    obtain ⟨b, j, hj, rfl⟩ := hv
    exact mul_mem (rootDiagUnit_mem_adjointGroup_of_det_one (Or.inr (Or.inl rfl)) b) hj
  exact RecipeFieldExcInn.eq_one_of_entrywise_eq_conj_F4 hf K hK ρ ⟨v, hvC⟩
    (MulEquiv.ext fun h => Subtype.ext ((coe_entrywiseAdjointAut _ ρ h).trans (hρ h.1 h.2)))

theorem innerFieldTrivial_E6 [Finite K] : InnerFieldTrivial TwistTag.E6.tag K := by
  obtain ⟨Θ, -, hΘ, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  intro ρ v hv hρ
  obtain ⟨b, j, hj, rfl⟩ := hv
  set α := entrywiseAdjointAut TwistTag.E6.tag ρ with hα
  have hg : rootDiagUnit TwistTag.E6.tag b * j * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈
      adjointGroup TwistTag.E6.tag K := conj_rootDiagUnit_mem_adjointGroup b hj
  have hα1 : Θ α = 1 := by
    refine (hker α).mpr ⟨⟨_, hg⟩, b, fun h => ?_⟩
    rw [hα, coe_entrywiseAdjointAut, hρ h h.2]
    change _ = rootDiagUnit TwistTag.E6.tag b * j * (rootDiagUnit TwistTag.E6.tag b)⁻¹ * _ * _ *
      _ * (rootDiagUnit TwistTag.E6.tag b * j * (rootDiagUnit TwistTag.E6.tag b)⁻¹)⁻¹
    group
  have hασ := hΘ α 1 1 ρ ⟨0, exactE_pos _⟩ fun h => by
    rw [hα, coe_entrywiseAdjointAut, rootDiagUnit_one]
    change _ = _ * _ * exactQ TwistTag.E6.tag K 0 * _ * (exactQ TwistTag.E6.tag K 0)⁻¹ * _ * _
    rw [exactQ_zero]
    simp
  rw [hα1] at hασ
  exact (congrArg Prod.fst hασ).symm

end RecipeExcLang

end CFSG.StandardType
