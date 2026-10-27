module

public import CFSG.Sporadic.Co2Rank3.Recognition

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup MulAction CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert

@[expose] def Co2RecognitionData (G : Type*) [Group G] : Prop :=
  Nat.card G = 42305421312000 ∧
    ∃ (G₁ : Subgroup G) (ψ : G₁ ≃* co2P0) (u v : G),
      (∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 3 = 3 → u * h * u⁻¹ ∈ G₁) ∧
        u ∉ normalizer (G₁ : Set G) ∧
        (∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 1 = 1 → v * h * v⁻¹ ∈ G₁) ∧
        v ∉ normalizer (G₁ : Set G)

theorem nonempty_mulEquiv_co2_of_data
    {G : Type*} [Group G] (h : Co2RecognitionData G) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2) := by
  obtain ⟨hcard, G₁, ψ, u, v, hu, hun, hv, hvn⟩ := h
  exact nonempty_mulEquiv_co2_of_le ψ hcard hu hun hv hvn

end CFSG.Sporadic.Co2Smith
