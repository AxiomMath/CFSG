module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Par
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3KGap

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2
  CFSG.Quasithin.F6.GoldAmLarge

namespace F6

namespace GoldAmLab4

@[expose] def B3DoublyMovedNoFiveInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D) (x c : D)
    (V₂ : Subgroup D), OneSide A B z V → OneSide B A c V₂ → 32 ≤ Nat.card ↥(A ⊓ B) →
      x ∈ B → x * x * x = 1 → x * z * x⁻¹ ≠ z →
      c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) → (∃ g ∈ A, g * c * g⁻¹ ≠ c) →
        ¬ 5 ≤ critDist (A ⊔ B) A B V

theorem b3MovedNoFourInput_of_inputs (hl : GoldAmL3K.B3NoFourInput.{u})
    (h5 : B3DoublyMovedNoFiveInput.{u}) : B3MovedNoFourInput.{u} := by
  intro D _ _ A B z V h h32 hn hVQ hb hU hmove h4
  have h1 : OneSide A B z V := ⟨h, hn, hVQ, hU⟩
  obtain ⟨x, c, V₂, hxB, hx3, hxz, hc, h2⟩ := exists_swap h h32 hn hmove
  by_cases hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c
  · have hU4 := le_coreIn_left_of_swap h1 h2 hxB hx3 hxz hc
    exact h5 D A B z V x c V₂ h1 h2 h32 hxB hx3 hxz hc hAc
      (five_le_critDist_of_moves_moves h1 h2 hxB hx3 hxz hc hU4 hAc)
  · push Not at hAc
    exact hl D B A c V₂ ⟨h2.gold, h2.nat, hAc, h2.abel⟩
      (four_le_critDist_swap h1 h2 hxB hx3 hxz hc)

theorem b3MovedCardBound_of_noFour_inputs (hl : GoldAmL3K.B3NoFourInput.{u})
    (h5 : B3DoublyMovedNoFiveInput.{u}) : B3MovedCardBound.{u} :=
  b3MovedCardBound_of_noFour (b3MovedNoFourInput_of_inputs hl h5)

theorem b3LabelInput_of_noFour_inputs (hl : GoldAmL3K.B3NoFourInput.{u})
    (h5 : B3DoublyMovedNoFiveInput.{u}) : B3LabelInput.{u} :=
  b3LabelInput_of_movedCardBound (b3MovedCardBound_of_noFour_inputs hl h5)

end GoldAmLab4

end F6

end CFSG.Quasithin
