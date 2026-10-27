module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Card

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D]

structure TwoNat (A B : Subgroup D) (z : D) (V : Subgroup D) (c : D) (V₂ : Subgroup D) : Prop where
  gold : GoldHyp A B
  card_ge : 32 ≤ Nat.card ↥(A ⊓ B)
  nat : IsNaturalAt A (A ⊓ B) z V
  nat₂ : IsNaturalAt B (A ⊓ B) c V₂
  V_le : V ≤ pCoreOf 2 B
  V₂_le : V₂ ≤ pCoreOf 2 A
  moves_z : ∃ y ∈ B, y * z * y⁻¹ ≠ z
  moves_c : ∃ g ∈ A, g * c * g⁻¹ ≠ c

theorem TwoNat.of_oneSide {A B : Subgroup D} {z c : D} {V V₂ : Subgroup D}
    (h : OneSide A B z V) (h2 : OneSide B A c V₂) (h32 : 32 ≤ Nat.card ↥(A ⊓ B))
    (hz : ∃ y ∈ B, y * z * y⁻¹ ≠ z) (hc : ∃ g ∈ A, g * c * g⁻¹ ≠ c) :
    TwoNat A B z V c V₂ where
  gold := h.gold
  card_ge := h32
  nat := h.nat
  nat₂ := by have := h2.nat; rwa [inf_comm] at this
  V_le := h.hVQ
  V₂_le := h2.hVQ
  moves_z := hz
  moves_c := hc

theorem index_two_inv_mul_mem {H K : Subgroup D} (h2 : H.relIndex K = 2) {x y : D} (hx : x ∈ K)
    (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  obtain ⟨a, haK, -, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp h2
  have h1 : a * x ∈ H := (hall x hx).resolve_right hxH
  have h2' : a * y ∈ H := (hall y hy).resolve_right hyH
  have := H.mul_mem (H.inv_mem h1) h2'
  have e : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group
  rwa [e] at this

section Vertex

variable (A B : Subgroup D)

@[expose] noncomputable def Nm (V V₂ : Subgroup D) : CosetGeom (A ⊔ B) A B → Subgroup D
  | Sum.inl x => Vv0 V x
  | Sum.inr y => Vv0 V₂ y

variable {A B} {V V₂ : Subgroup D}

theorem Nm_smul (hA : A ≤ Subgroup.normalizer (V : Set D))
    (hB : B ≤ Subgroup.normalizer (V₂ : Set D)) (g : ↥(A ⊔ B)) (γ : CosetGeom (A ⊔ B) A B) :
    Nm A B V V₂ (g • γ) = conjSub (g : D) (Nm A B V V₂ γ) := by
  cases γ with
  | inl x => exact Vv0_smul hA g x
  | inr y => exact Vv0_smul hB g y

theorem Nm_γ₀ (hA : A ≤ Subgroup.normalizer (V : Set D)) :
    Nm A B V V₂ (γ₀ (A ⊔ B) A B) = V := by
  have := Vv0_mk (G₀ := A ⊔ B) hA (1 : ↥(A ⊔ B))
  simpa [Nm, γ₀, conjSub_one] using this

theorem Nm_γ₁ (hB : B ≤ Subgroup.normalizer (V₂ : Set D)) :
    Nm A B V V₂ (γ₁ (A ⊔ B) A B) = V₂ := by
  have := Vv0_mk (G₀ := A ⊔ B) hB (1 : ↥(A ⊔ B))
  simpa [Nm, γ₁, conjSub_one] using this

end Vertex

end GoldAmLab6

end F6

end CFSG.Quasithin
