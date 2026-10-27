module

public import CFSG.LocalAnalysis.StandardType.GGRawTorusPClassicalTwo
public import CFSG.LocalAnalysis.StandardType.GGRawTorusPProofModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly RawTorusPClassical

theorem ringEquiv_eq_refl_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (σ : K ≃+* K) (x : K) : σ x = x := by
  classical
  have := Fintype.ofFinite K
  have hx : x ^ 2 = x := by
    have h1 := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at h1
  have h01 : x = 0 ∨ x = 1 := by
    have h2 : x * (x - 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases h01 with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

end CFSG.StandardType

end
