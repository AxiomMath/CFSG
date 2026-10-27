module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Final

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2
  CFSG.Quasithin.F6.GoldAmLab4

namespace F6

namespace GoldAmLab5

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
  {c : D} {V₂ : Subgroup D}

theorem doublyMoved_five_le (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) (hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c) :
    5 ≤ critDist (A ⊔ B) A B V :=
  five_le_critDist_of_moves_moves h h2 hxB hx3 hxz hc
    (le_coreIn_left_of_swap h h2 hxB hx3 hxz hc) hAc

@[expose] def DoublyMovedEmpty : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D) (x c : D)
    (V₂ : Subgroup D), OneSide A B z V → OneSide B A c V₂ → 32 ≤ Nat.card ↥(A ⊓ B) →
      x ∈ B → x * x * x = 1 → x * z * x⁻¹ ≠ z →
      c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) → (∃ g ∈ A, g * c * g⁻¹ ≠ c) → False

theorem b3DoublyMovedNoFiveInput_iff : B3DoublyMovedNoFiveInput.{u} ↔ DoublyMovedEmpty.{u} :=
  ⟨fun h5 D _ _ A B z V x c V₂ h h2 h32 hxB hx3 hxz hc hAc =>
    h5 D A B z V x c V₂ h h2 h32 hxB hx3 hxz hc hAc (doublyMoved_five_le h h2 hxB hx3 hxz hc hAc),
  fun he D _ _ A B z V x c V₂ h h2 h32 hxB hx3 hxz hc hAc _ =>
    he D A B z V x c V₂ h h2 h32 hxB hx3 hxz hc hAc⟩

end GoldAmLab5

end F6

end CFSG.Quasithin
