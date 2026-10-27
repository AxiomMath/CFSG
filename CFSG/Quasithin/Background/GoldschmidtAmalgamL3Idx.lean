module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem relIndex_ne_zero_of_finite (H K : Subgroup D) : H.relIndex K ≠ 0 := by
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem card_inf_ne_two : Nat.card ↥(A ⊓ B) ≠ 2 := by
  have hVT : V ≤ A ⊓ B := h.natural.le_pCoreOf.trans h.gold.pCoreOf_left_le
  have := Subgroup.card_le_of_le hVT
  rw [h.natural.card_eq] at this
  omega

theorem relIndex_inf_pCoreOf_T :
    (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (A ⊓ B) = 4 :=
  h.gold.relIndex_inf_pCoreOf (h.gold.pCoreOf_ne h.card_inf_ne_two)

theorem relIndex_inf_pCoreOf_left :
    (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 A) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) (pCoreOf 2 A) (A ⊓ B)
    inf_le_left h.gold.pCoreOf_left_le
  rw [h.relIndex_inf_pCoreOf_T, h.gold.relIndex_pCoreOf_T_left] at h1
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
