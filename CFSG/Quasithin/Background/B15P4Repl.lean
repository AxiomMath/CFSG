module

public import CFSG.Quasithin.Background.B1Restrict
public import Mathlib

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem exists_quadratic_offender_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    ∃ F : Subgroup (MulAut V), F ≤ A ∧ IsFFStarOffender X F ∧ IsQuadratic F ∧
      Nat.card F * Nat.card (fixV F) = Nat.card A * Nat.card (fixV A) ∧
      IsFFStarMin X F ∧ FFLe X F A := by
  obtain ⟨F, hFA, hFmin⟩ := B1.exists_isFFStarMin_le hA
  exact ⟨F, hFA.2.2.1, hFmin.1, B1_4_3 hV hFmin, hFA.2.2.2, hFmin, hFA⟩

theorem card_fixV_Bv [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (v : V) :
    (B1.Bv A v).relIndex A * Nat.card (fixV A) = Nat.card (fixV (B1.Bv A v)) := by
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.2.2.1.1
  have h1 := B1.card_index_mul_le hc v
  have h2 := hA.card_le (B1.Bv_le A v)
  have h3 := B1.relIndex_mul_card_Bv A v
  have hpos : 0 < Nat.card (B1.Bv A v) := Nat.card_pos
  refine le_antisymm h1 ?_
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card (B1.Bv A v) * Nat.card (fixV (B1.Bv A v))
      ≤ Nat.card A * Nat.card (fixV A) := h2
    _ = (B1.Bv A v).relIndex A * Nat.card (B1.Bv A v) * Nat.card (fixV A) := by rw [h3]
    _ = Nat.card (B1.Bv A v) * ((B1.Bv A v).relIndex A * Nat.card (fixV A)) := by ring

theorem exists_proper_offender_below_of_not_quadratic [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (hq : ¬ IsQuadratic A) :
    ∃ B : Subgroup (MulAut V), B < A ∧ IsFFStarOffender X B ∧ FFLe X B A := by
  by_contra hcon
  push Not at hcon
  apply hq
  refine B1_4_3 hV ⟨hA, fun B hB hBA => ?_⟩
  by_contra hne
  exact hcon B (lt_of_le_of_ne hBA.2.2.1 hne) hB hBA

end CFSG.Quasithin
