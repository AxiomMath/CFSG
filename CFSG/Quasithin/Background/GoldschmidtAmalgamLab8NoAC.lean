module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Sys

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7 CFSG.Quasithin.F6.GoldAmL3

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

@[expose] def AMovedEmpty (A B : Subgroup D) (_z : D) (_V : Subgroup D) : Prop :=
  ∀ (c : D) (V₂ : Subgroup D), IsNaturalAt B (A ⊓ B) c V₂ → (∃ g ∈ A, g * c * g⁻¹ ≠ c) → False

end GoldAmLab8

end F6

end CFSG.Quasithin
