module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CCount
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

variable {R : Type} [Group R]

theorem card_sqrt_quaternion :
    Nat.card {x : QuaternionGroup 2 // x * x = 1} ≤ 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem le_normalizer_of_commute {A B : Subgroup R} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set R) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have : a * b * a⁻¹ = b := by rw [hc a ha b hb]; group
    rwa [this]
  · intro hb
    have h1 := hc a⁻¹ (A.inv_mem ha) _ hb
    have : b = a * b * a⁻¹ :=
      calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
        _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h1]
        _ = a * b * a⁻¹ := by group
    rwa [this]

theorem card_centralProduct
    (hcp : F6.IsCentralProduct₂ R (QuaternionGroup 2) (QuaternionGroup 2)) : Nat.card R = 32 := by
  obtain ⟨A, B, hAB, hc, ⟨eA⟩, ⟨eB⟩, h2⟩ := hcp
  have hprod := card_sup_mul_card_inf (le_normalizer_of_commute hc)
  have hA : Nat.card A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hAB, Subgroup.card_top, h2, hA, hB] at hprod
  omega

theorem card_le_eight_of_centralProduct [Finite R]
    (hcp : F6.IsCentralProduct₂ R (QuaternionGroup 2) (QuaternionGroup 2)) (W : Subgroup R)
    (hW : ∀ w ∈ W, w * w = 1) : Nat.card W ≤ 8 := by
  have hR := card_centralProduct hcp
  obtain ⟨A, B, hAB, hc, ⟨eA⟩, ⟨eB⟩, h2⟩ := hcp
  have hBn : (⊤ : Subgroup R) ≤ Subgroup.normalizer (B : Set R) := by
    rw [← hAB]
    exact sup_le (le_normalizer_of_commute hc) Subgroup.le_normalizer
  have hprod := card_sup_mul_card_inf (A := W) (B := B) (fun w _ => hBn trivial)
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hinf : Nat.card ↥(W ⊓ B) ≤ 2 := card_inf_le_of_mulEquiv eB hW card_sqrt_quaternion
  have hsup : Nat.card ↥(W ⊔ B) ≤ 32 := hR ▸ Subgroup.card_le_card_group _
  have := Nat.mul_le_mul hsup hinf
  rw [hB] at hprod
  omega

end Y15111

end CFSG.Quasithin
