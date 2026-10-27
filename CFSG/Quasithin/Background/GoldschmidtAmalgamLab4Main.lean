module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Crit

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2
  CFSG.Quasithin.F6.GoldAmLarge

namespace F6

namespace GoldAmLab4

@[expose] def B3MovedNoFourInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp A B → 32 ≤ Nat.card ↥(A ⊓ B) → IsNaturalAt A (A ⊓ B) z V → V ≤ pCoreOf 2 B →
      3 ≤ critDist (A ⊔ B) A B V → IsElemAbelian 2 (conjClosure V B) →
        (∃ y ∈ B, y * z * y⁻¹ ≠ z) → ¬ 4 ≤ critDist (A ⊔ B) A B V

theorem b3MovedCardBound_of_noFour (h4 : B3MovedNoFourInput.{u}) : B3MovedCardBound.{u} := by
  intro D _ _ A B z V h h32 hn hVQ hb hU hmove
  exact absurd (four_le_critDist_of_moves ⟨h, hn, hVQ, hU⟩ h32 hmove)
    (h4 D A B z V h h32 hn hVQ hb hU hmove)

end GoldAmLab4

end F6

end CFSG.Quasithin
