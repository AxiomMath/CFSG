module

public import CFSG.Milestones.ASVolI.F411.Ident

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

variable {E : Type} [Group E]

theorem burnsideF411_swap_of_card_ne {M₁ M₂ : Subgroup E} (h : Nat.card M₁ ≠ Nat.card M₂) :
    burnsideF411_Swap M₁ M₂ := by
  intro χ₁ χ₂ hχ₁ _ hr₁ _ _
  exfalso
  apply h
  rw [← hr₁]
  exact Nat.card_congr (MonoidHom.ofInjective hχ₁).toEquiv

theorem burnsideF411_card_eq_mul_index [Finite E] {Gp M : Subgroup E} (hN : Gp.Normal)
    (hGM : Gp ⊔ M = ⊤) : Nat.card M = Gp.index * Nat.card (Gp ⊓ M : Subgroup E) := by
  have h1 := Subgroup.relIndex_mul_card Gp M
  have hrel : Gp.relIndex M = Gp.index := by
    rw [← Subgroup.relIndex_sup_left, hGM, Subgroup.relIndex_top_right]
  rw [hrel] at h1
  exact h1.symm

theorem burnsideF411_swap_of_relIndex_ne [Finite E] {Gp M₁ M₂ : Subgroup E} (hN : Gp.Normal)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (h : (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) ≠ (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂)) :
    burnsideF411_Swap M₁ M₂ := by
  refine burnsideF411_swap_of_card_ne fun hc => h ?_
  have h1 := burnsideF411_card_eq_mul_index hN (burnsideF411_sup_eq_top inf_le_left hsplit)
  have h2 := burnsideF411_card_eq_mul_index hN (burnsideF411_sup_eq_top inf_le_right hsplit)
  have hB1 : Gp ⊓ (M₁ ⊓ M₂) ≤ Gp ⊓ M₁ := inf_le_inf_left _ inf_le_left
  have hB2 : Gp ⊓ (M₁ ⊓ M₂) ≤ Gp ⊓ M₂ := inf_le_inf_left _ inf_le_right
  have c1 := Subgroup.relIndex_mul_card (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁)
  have c2 := Subgroup.relIndex_mul_card (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₂)
  rw [inf_of_le_left hB1] at c1
  rw [inf_of_le_left hB2] at c2
  have hpos : 0 < Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) :=
    Nat.mul_pos (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) Nat.card_pos
  have : Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) *
        (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) =
      Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) *
        (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) := by
    calc Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) * (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁)
        = Gp.index * ((Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) *
            Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E)) := by ring
      _ = Nat.card M₁ := by rw [c1, h1]
      _ = Nat.card M₂ := hc
      _ = Gp.index * ((Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) *
            Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E)) := by rw [c2, h2]
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

end CFSG.ASVolI
