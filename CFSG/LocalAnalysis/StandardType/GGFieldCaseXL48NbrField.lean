module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48TailCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

@[expose] def GGRawFieldNotComm (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => ∀ f ∈ F, orderOf f = p → f ∉ ggInndiag R I ⊔ ⁅(⊤ : Subgroup (MulAut R)), ⊤⁆

@[expose] def GGRawFieldNotCommInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard (GGRawFieldNotComm p))

section GroupTheory

variable {G : Type} [Group G]

theorem not_mem_commutator_sup_of_ggLAut {K U₁ : Subgroup G} {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (T : Subgroup (MulAut R))
    (hT : ⁅(⊤ : Subgroup (MulAut R)), ⊤⁆ ≤ T) (hU₁N : U₁ ≤ Subgroup.normalizer (K : Set G))
    (hU₁ : ∀ (u : G) (hu : u ∈ Subgroup.normalizer (K : Set G)), u ∈ U₁ → ggLAut K θ ⟨u, hu⟩ ∈ T)
    {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hxT : ggLAut K θ ⟨x, hxN⟩ ∉ T) :
    x ∉ ⁅Subgroup.normalizer (K : Set G), Subgroup.normalizer (K : Set G)⁆ ⊔ U₁ := by
  intro hx
  have hle : ⁅Subgroup.normalizer (K : Set G), Subgroup.normalizer (K : Set G)⁆ ⊔ U₁ ≤
      (T.comap (ggLAut K θ)).map (Subgroup.normalizer (K : Set G)).subtype := by
    refine sup_le ?_ fun u hu => ⟨⟨u, hU₁N hu⟩, hU₁ u (hU₁N hu) hu, rfl⟩
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : Subgroup.normalizer (K : Set G)), ⟨b, hb⟩⁆, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement]
      exact hT (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · rw [map_commutatorElement]
      rfl
  obtain ⟨n, hn, hnx⟩ := hle hx
  obtain rfl : n = ⟨x, hxN⟩ := Subtype.ext hnx
  exact hxT hn

end GroupTheory

theorem ggL48NbrFieldInput_of_raw (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hnc : GGRawFieldNotCommInput) : GGL48NbrFieldInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  have hcfg := ggL45Config_of_setup hS
  obtain ⟨R, _, I, F, θ, hs, hna, -, hNC, -, ⟨f, hf, u, hu, hord, hxind⟩, hiff⟩ :=
    ggL4546_exists_marking (P' := LargeEvenSimpleGuard (GGRawFieldNotComm p))
      (hnc p hcfg.prime hcfg.odd) hraw hiso hcfg
  have hUK := hcfg.le_normalizer
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have huT : u ∈ ggInndiag R I ⊔ ⁅(⊤ : Subgroup (MulAut R)), ⊤⁆ :=
    Subgroup.mem_sup_left (subset_ggInndiag hu)
  refine not_mem_commutator_sup_of_ggLAut θ _ le_sup_right (hcfg.part_le.trans hUK)
    (fun v hv hvU₁ => Subgroup.mem_sup_left
      (subset_ggInndiag ((hiff v (hcfg.part_le hvU₁) hv).mp hvU₁)))
    (hUK hxU) fun hxT => hNC hs hna f hf hord ?_
  have h2 : u * f * u⁻¹ = ggLAut K θ ⟨x⁻¹, inv_mem (hUK hxU)⟩ :=
    eq_ggLAut_of_induces K θ (hUK hxU) hxind
  have h3 : ggLAut K θ ⟨x⁻¹, inv_mem (hUK hxU)⟩ = (ggLAut K θ ⟨x, hUK hxU⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have e : f = u⁻¹ * (u * f * u⁻¹) * u := by group
  rw [e, h2, h3]
  exact mul_mem (mul_mem (inv_mem huT) (inv_mem hxT)) huT

end CFSG.StandardType
