module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Centre
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Sys

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem TwoSys.of_goldHyp3 (h3 : GoldAmL3.GoldHyp3 A B z V) (h32 : 32 ≤ Nat.card ↥(A ⊓ B))
    (hn₂ : IsNaturalAt B (A ⊓ B) c V₂) : TwoSys A B z V c V₂ where
  gold := h3.gold
  card_ge := h32
  nat := h3.natural
  nat₂ := hn₂
  V_le := h3.le_pCoreOf_right
  V₂_le := by
    have h32' : 32 ≤ Nat.card ↥(B ⊓ A) := by rwa [inf_comm]
    have hn₂' : IsNaturalAt B (B ⊓ A) c V₂ := by rw [inf_comm]; exact hn₂
    exact hn₂'.le_pCoreOf_of_large h3.gold.symm h32'

end GoldAmLab7

end F6

end CFSG.Quasithin
