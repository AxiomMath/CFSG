module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Red

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3K

open GoldAmL3

@[expose] def B3NoFourInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → ¬ 4 ≤ critDist (A ⊔ B) A B V

@[expose] def B3IntersectionInputThree : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → critDist (A ⊔ B) A B V = 3 →
      ∃ y ∈ A, coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ⊓
        conjSub y (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) ≤ V

theorem b3IntersectionInput_of_inputs (h3 : B3IntersectionInputThree.{u})
    (h4 : B3NoFourInput.{u}) : B3IntersectionInput.{u} := by
  intro D _ _ A B z V h
  have hb : critDist (A ⊔ B) A B V = 3 := by
    have h1 := h.three_le_critDist
    have h2 := h4 D A B z V h
    omega
  exact h3 D A B z V h hb

end GoldAmL3K

end F6

end CFSG.Quasithin
