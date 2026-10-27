module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6OddCoreTools
public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem oddCore_inf_centralizer_eq_bot_of_derivedFixed {G : Type*} [Group G] {C J : Subgroup G}
    [Finite C] {η : MulAut C} (hD : DerivedFixedSubgroupData C J η)
    (hcent : Subgroup.centralizer {η} ⊓ Subgroup.centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = Subgroup.zpowers η)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {η}) = ⊥ := by
  obtain ⟨hord, hJC, -, -, hJs, hJe, hinj, hNη, hNnorm⟩ := hD
  have hη : η ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one η
  exact oddCore_inf_centralizer_eq_bot_of_simple hη hJC hJs hJe hinj hNη hNnorm hcent H hIH

theorem even_E6_nontrivial_field_projection_involution_full_centralizer_odd_core {f : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (Θ : MulAut (adjointGroup TwistTag.E6.tag K) →*
      RingAut K × Multiplicative (ZMod (exactE TwistTag.E6.tag)))
    (hΘ : ∀ (β : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE TwistTag.E6.tag)),
      (∀ h : adjointGroup TwistTag.E6.tag K, (β h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          exactQ TwistTag.E6.tag K ε * Units.map (entrywiseHom σ.toRingHom)
            (h : ModGL TwistTag.E6.tag K) * (exactQ TwistTag.E6.tag K ε)⁻¹ *
              (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹) →
      Θ β = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE TwistTag.E6.tag))))
    (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag K)))
    (hIH : inner (adjointGroup TwistTag.E6.tag K) ≤ H)
    {α : MulAut (adjointGroup TwistTag.E6.tag K)} (hα : orderOf α = 2) (hΘα : (Θ α).1 ≠ 1) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (adjointGroup TwistTag.E6.tag K) := generated_group_finite _ K
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hΘα' := hΘ α g a σ ε hga
  have hσ1 : σ ≠ 1 := by
    rw [hΘα'] at hΘα
    exact hΘα
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : Θ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    rw [hΘα', Prod.pow_mk, Prod.mk_eq_one] at h1
    exact h1.1
  obtain ⟨-, -, -, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ1
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
  obtain ⟨hQ1, hQP⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
  have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega
  have hconj : ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K), φ * α * φ⁻¹ =
      diagramConjAut TwistTag.E6 K ^ (ε : ℕ) * entrywiseAdjointAut TwistTag.E6.tag σ := by
    rcases hε2 with h0 | h1
    · obtain ⟨_, -, hdesc⟩ := hQ1 TwistTag.E6.tag
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * Units.map (entrywiseHom σ.toRingHom)
            (u : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h0, exactQ_zero, mul_one, inv_one, mul_one]
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
      refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_⟩
      rw [hψ u, h0, pow_zero, one_mul, coe_entrywiseAdjointAut]
    · obtain ⟨_, -, hdesc⟩ := hQP
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h1]
        rfl
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
      refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_⟩
      rw [hψ u, h1, pow_one, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
  obtain ⟨φ, hφ⟩ := hconj
  refine oddCore_inf_centralizer_conj_eq_bot (fun H' hIH' => ?_) H hIH hφ
  obtain ⟨hD0, hD1⟩ := even_E6_canonical_field_graph_field_derived_fixed_subgroups he1 K hK' σ hσ'
  obtain ⟨hc0, hc1⟩ :=
    even_E6_canonical_field_graph_field_pointwise_centralizers he1 K hK' σ hσ'
  rcases hε2 with h0 | h1
  · rw [h0]
    exact oddCore_inf_centralizer_eq_bot_of_derivedFixed hD0 hc0 H' hIH'
  · rw [h1]
    exact oddCore_inf_centralizer_eq_bot_of_derivedFixed hD1 hc1 H' hIH'

end CFSG.RankThree.Chevalley
