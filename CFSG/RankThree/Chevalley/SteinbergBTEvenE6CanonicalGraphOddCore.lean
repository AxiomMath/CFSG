module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6OddCoreTools
public import CFSG.LieType.Chevalley.EvenTwistedE6CanonicalGraphPointwiseCentralizer

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem oddCore_inf_centralizer_eq_bot_of_canonicalGraph {G : Type*} [Group G]
    {C J : Subgroup G} [Finite C] {P : G} (hD : CanonicalGraphFixedSubgroup C J P)
    {η : MulAut C} (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hcent : Subgroup.centralizer {η} ⊓ Subgroup.centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = Subgroup.zpowers η)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {η}) = ⊥ := by
  obtain ⟨η₀, hη₀, hord, hJC, -, hJs, hJe, hinj, hNη, hNnorm⟩ := hD
  have e : η₀ = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, hη])
  subst e
  have hη2 : η₀ ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one η₀
  exact oddCore_inf_centralizer_eq_bot_of_simple hη2 hJC hJs hJe hinj hNη hNnorm hcent H hIH

theorem even_E6_canonical_graph_class_odd_core {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) (η : MulAut (adjointGroup TwistTag.E6.tag k))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹)
    (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)))
    (hIH : inner (adjointGroup TwistTag.E6.tag k) ≤ H)
    {α φ : MulAut (adjointGroup TwistTag.E6.tag k)} (hα : φ * α * φ⁻¹ = η) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite (adjointGroup TwistTag.E6.tag k) := generated_group_finite _ k
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hD := canonicalGraphFixedSubgroup_adjointGroup k hf hk h2
  rw [map_baseChangeGL_id] at hD
  have hηγ : η = diagramConjAut TwistTag.E6 k :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη, coe_diagramConjAut])
  have hcent := even_E6_canonical_graph_full_pointwise_centralizer hf k hk
  rw [← hηγ] at hcent
  exact oddCore_inf_centralizer_conj_eq_bot
    (fun H' hIH' => oddCore_inf_centralizer_eq_bot_of_canonicalGraph hD hη hcent H' hIH') H hIH hα

theorem even_twisted_E6_canonical_graph_class_odd_core {f : ℕ} (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹)
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))
    (hIH : inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H)
    {α φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ)} (hα : φ * α * φ⁻¹ = η) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, hD, -⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  have hcent := even_twisted_E6_canonical_graph_full_pointwise_centralizer hf k K hk hK σ hσ η hη
  exact oddCore_inf_centralizer_conj_eq_bot
    (fun H' hIH' => oddCore_inf_centralizer_eq_bot_of_canonicalGraph hD hη hcent H' hIH') H hIH hα

theorem even_E6_twisted_E6_canonical_graph_class_full_centralizer_odd_core (f : ℕ) (hf : 1 ≤ f)
    (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∀ η : MulAut (adjointGroup TwistTag.E6.tag k), (∀ g, (η g : ModGL TwistTag.E6.tag k) =
        diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) →
      ∀ H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)),
        inner (adjointGroup TwistTag.E6.tag k) ≤ H → ∀ α ∈ H,
          (∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = η) →
            CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) ∧
    (∀ η : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∀ g, (η g : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) →
      ∀ H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)),
        inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H → ∀ α ∈ H,
          (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = η) →
            CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) :=
  ⟨fun η hη H hIH _ _ ⟨_, hα⟩ => even_E6_canonical_graph_class_odd_core hf k hk η hη H hIH hα,
    fun η hη H hIH _ _ ⟨_, hα⟩ =>
      even_twisted_E6_canonical_graph_class_odd_core hf k K hk hK σ hσ η hη H hIH hα⟩

end CFSG.RankThree.Chevalley
