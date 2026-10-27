module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S6Card
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SCard

public section

universe u

namespace CFSG.Quasithin

open CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL3

@[expose] def B5LeNoACInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → 5 ≤ critDist (A ⊔ B) A B V → Nat.card (conjClosure V B) = 16 →
      NoACentral A B

theorem b5CardInput_of_b5LeNoAC (hA : B5LeNoACInput.{u}) : B5CardInput.{u} := by
  intro D _ _ A B z V h hb
  rcases h.card_conjClosure_eq with h8 | h16
  · exact h8
  · exact b5CardInputNoAC D A B z V h (hA D A B z V h (by omega) h16) hb

end GoldAmL3

end F6

end CFSG.Quasithin
