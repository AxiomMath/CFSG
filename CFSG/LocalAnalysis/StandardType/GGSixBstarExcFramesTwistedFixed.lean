module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedField
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFixedField
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.Open

section FixedTw


theorem exists_fixedElemAbelian_twistedE6 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {δ : K ≃+* K} (hδ : δ ^ p = 1)
    (hdata : ∀ f₀ : ℕ, 1 ≤ f₀ → ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      Nat.card K₀ = (2 ^ f₀) ^ 2 → ∀ σ₀ : K₀ ≃+* K₀, (∀ c, σ₀ c = c ^ 2 ^ f₀) →
        ((2 ^ f₀ : ℕ) : ZMod p) = ((2 ^ f : ℕ) : ZMod p) →
          SylowTorus ↥(twistedE6RootGroup K₀ σ₀) p m) :
    ∃ E : Subgroup (ModGL TwistTag.E6.tag K), E ≤ twistedE6RootGroup K σ ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ m ∧
        ∀ e ∈ E, Units.map (entrywiseHom δ.toRingHom) e = e := by
  obtain ⟨f₀, hf₀, hcard, hpow, hmod⟩ := exists_fixSubfield_twisted hf hK hp2 hδ
  haveI : Finite (fixSubfield δ) := Subtype.finite
  set σ₀ : fixSubfield δ ≃+* fixSubfield δ := fixSubfieldRestrict σ δ with hσ₀def
  have hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ f₀ := fun c => by
    refine Subtype.ext ?_
    rw [hσ₀def, coe_fixSubfieldRestrict, hσ, SubmonoidClass.coe_pow]
    exact hpow c
  obtain ⟨E₀, hE₀, hE₀c⟩ := (hdata f₀ hf₀ (fixSubfield δ) hcard σ₀ hσ₀ hmod).exists_elemAbelian
  set ι : fixSubfield δ →+* K := (fixSubfield δ).subtype with hιdef
  have hσι : ∀ c : fixSubfield δ, σ.toRingHom (ι c) = ι (σ₀.toRingHom c) := fun c =>
    (coe_fixSubfieldRestrict σ δ c).symm
  have hle := map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (σ := σ₀.toRingHom)
    (Fr := σ.toRingHom) (ι := ι) σ₀.surjective hσι
  refine ⟨(E₀.map (twistedE6RootGroup (fixSubfield δ) σ₀).subtype).map (baseChangeGL ι), ?_,
    isElemAbelian_map_frame _ (isElemAbelian_map_frame _ hE₀), ?_, ?_⟩
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    exact hle ⟨c, c.2, rfl⟩
  · rw [Subgroup.card_map_of_injective (baseChangeGL_injective ι),
      Subgroup.card_map_of_injective Subtype.val_injective, hE₀c]
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    exact units_map_entrywise_baseChangeGL ι δ (fun x => x.2) _

end FixedTw

end ExcFrames

end CFSG.StandardType
