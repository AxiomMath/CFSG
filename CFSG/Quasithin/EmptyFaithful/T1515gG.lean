module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.T1515gA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def A7InducesPerm (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7)) (g : G)
    (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ ℓ ℓ' : ↥L, (ℓ' : G) = g * ℓ * g⁻¹ →
    (α ℓ' : Equiv.Perm (Fin 7)) = σ * (α ℓ : Equiv.Perm (Fin 7)) * σ⁻¹

@[expose] def A7SigmaStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)),
    IsShort2 L → A7Str L α β →
    ∀ (P : Finset (Finset (Fin 7))) (d : Fin 7), IsPartitionOfType P {2, 2, 2, 1} → {d} ∈ P →
    ∃ σ₀ : Equiv.Perm (Fin 7), A7IsThreeSwaps σ₀ ∧
      ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) →
        g ∈ Subgroup.centralizer (a7Y1Of L α P : Set G) →
        ∃ σ : Equiv.Perm (Fin 7), (σ = 1 ∨ σ = σ₀) ∧ A7InducesPerm L α g σ ∧ A7ActsOnU L β g σ

@[expose] def A7CohomStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)),
    IsShort2 L → A7Str L α β →
    ∀ (P : Finset (Finset (Fin 7))) (d : Fin 7), IsPartitionOfType P {2, 2, 2, 1} → {d} ∈ P →
    ∀ u : ↥(blockU L),
      (QuotientAddGroup.mk (a7ETheta d) : AltHeart 7) = Multiplicative.toAdd (β u) →
      ∀ h : G, h ∈ Subgroup.normalizer (L : Set G) → A7InducesPerm L α h 1 →
        h ∈ Subgroup.centralizer (a7Y1Of L α P : Set G) →
        ∃ c ∈ Subgroup.centralizer (L : Set G), ∃ k : ℤ, h = c * (u : G) ^ k

theorem a7ModuleStepA_of_steps (hSig : A7SigmaStep) (hZ : A7CohomStep) : A7ModuleStepA := by
  intro G _ _ L S α β hshort hstr hSL hUS P d hP hd u hu
  obtain ⟨σ₀, hσ₀, hSig'⟩ := hSig G L α β hshort hstr P d hP hd
  have huS : (u : G) ∈ S := hUS u.2
  have hB1 : ∀ g ∈ S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G), A7InducesPerm L α g 1 →
      g ∈ a7BSub S L (u : G) := by
    intro g hg hind
    obtain ⟨c, hc, k, hk⟩ := hZ G L α β hshort hstr P d hP hd u hu g (hSL hg.1) hind hg.2
    have hcS : c ∈ S := by
      have : c = g * (u : G) ^ (-k) := by rw [hk]; group
      rw [this]
      exact S.mul_mem hg.1 (S.zpow_mem huS _)
    rw [hk]
    exact Subgroup.mul_mem_sup ⟨hcS, hc⟩ (Subgroup.zpow_mem_zpowers _ _)
  by_cases hex : ∃ g ∈ S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G),
      A7InducesPerm L α g σ₀ ∧ A7ActsOnU L β g σ₀
  · right
    obtain ⟨g₀, hg₀, hind₀, hact₀⟩ := hex
    refine ⟨g₀, hg₀.1, ⟨σ₀, hact₀, hσ₀⟩, ?_⟩
    intro g hg
    obtain ⟨σ, hσ, hind, -⟩ := hSig' g (hSL hg.1) hg.2
    rcases hσ with h1 | h1
    · rw [h1] at hind
      exact Or.inl (hB1 g hg hind)
    · rw [h1] at hind
      right
      have hg0 : g * g₀⁻¹ ∈ S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G) :=
        (S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G)).mul_mem hg
          ((S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G)).inv_mem hg₀)
      have hn₀ : g₀ ∈ Subgroup.normalizer (L : Set G) := hSL hg₀.1
      have hind1 : A7InducesPerm L α (g * g₀⁻¹) 1 := by
        intro ℓ ℓ' h
        have hℓ₁ : g₀⁻¹ * (ℓ : G) * g₀ ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn₀) (ℓ : G)).mp ℓ.2
          simpa using this
        have e1 := hind₀ ⟨g₀⁻¹ * (ℓ : G) * g₀, hℓ₁⟩ ℓ (by simp; group)
        have e2 := hind ⟨g₀⁻¹ * (ℓ : G) * g₀, hℓ₁⟩ ℓ' (by
          have : (ℓ' : G) = g * g₀⁻¹ * (ℓ : G) * (g * g₀⁻¹)⁻¹ := h
          simp only [this]
          group)
        rw [e2, ← e1]
        simp
      exact ⟨g * g₀⁻¹, hB1 _ hg0 hind1, by group⟩
  · left
    intro g hg
    obtain ⟨σ, hσ, hind, hact⟩ := hSig' g (hSL hg.1) hg.2
    rcases hσ with h1 | h1
    · rw [h1] at hind
      exact hB1 g hg hind
    · exact absurd ⟨g, hg, h1 ▸ hind, h1 ▸ hact⟩ hex

end CFSG.Quasithin
