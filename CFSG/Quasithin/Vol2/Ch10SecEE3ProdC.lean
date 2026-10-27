module

public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

theorem fixV_le_fixV {X Y : Subgroup (MulAut W)} (h : Y ≤ X) : fixV X ≤ fixV Y :=
  fun _ hw y hy => hw y (h hy)

namespace ProdSetting

variable {W₁ W₂ : Subgroup W} {P₁ P₂ : Subgroup (MulAut W)} (h : ProdSetting W₁ W₂ P₁ P₂)
include h

noncomputable abbrev projOne (X : Subgroup (MulAut W)) : Subgroup (MulAut W) := h.symm.projTwo X

variable [Finite W]

theorem card_mul_card_fixV_le_aux
    (hb₁ : ∀ Y ≤ P₁, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₁) ≤ Nat.card W₁)
    (hb₂ : ∀ Y ≤ P₂, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₂) ≤ Nat.card W₂)
    {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂) :
    Nat.card X * Nat.card ↥(fixV X ⊓ (W₁ ⊔ W₂)) =
      (Nat.card ↥(X ⊓ P₁) * Nat.card ↥(fixV X ⊓ W₁)) *
        (Nat.card ↥(h.projTwo X) * Nat.card ↥(fixV (h.projTwo X) ⊓ W₂)) ∧
      Nat.card ↥(fixV X ⊓ W₁) ≤ Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁) ∧
      Nat.card ↥(X ⊓ P₁) * Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁) ≤ Nat.card W₁ ∧
      Nat.card ↥(h.projTwo X) * Nat.card ↥(fixV (h.projTwo X) ⊓ W₂) ≤ Nat.card W₂ := by
  refine ⟨?_, Subgroup.card_le_of_le (inf_le_inf_right _ (fixV_le_fixV inf_le_left)),
    hb₁ _ inf_le_right, hb₂ _ (h.projTwo_le X)⟩
  rw [h.card_eq_card_inf_mul_card_projTwo hX, h.card_fixV_inf_sup hX, h.fixV_inf_two hX]
  ring

theorem card_mul_card_fixV_le
    (hb₁ : ∀ Y ≤ P₁, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₁) ≤ Nat.card W₁)
    (hb₂ : ∀ Y ≤ P₂, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₂) ≤ Nat.card W₂)
    {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂) :
    Nat.card X * Nat.card ↥(fixV X ⊓ (W₁ ⊔ W₂)) ≤ Nat.card ↥(W₁ ⊔ W₂) := by
  obtain ⟨e, h1, h2, h3⟩ := h.card_mul_card_fixV_le_aux hb₁ hb₂ hX
  rw [e, h.card_sup]
  exact Nat.mul_le_mul ((Nat.mul_le_mul_left _ h1).trans h2) h3

theorem eq_of_card_mul_card_fixV_eq
    (hb₁ : ∀ Y ≤ P₁, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₁) ≤ Nat.card W₁)
    (hb₂ : ∀ Y ≤ P₂, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₂) ≤ Nat.card W₂)
    {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂)
    (heq : Nat.card X * Nat.card ↥(fixV X ⊓ (W₁ ⊔ W₂)) = Nat.card ↥(W₁ ⊔ W₂)) :
    Nat.card ↥(X ⊓ P₁) * Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁) = Nat.card W₁ ∧
      Nat.card ↥(fixV X ⊓ W₁) = Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁) ∧
      Nat.card ↥(h.projTwo X) * Nat.card ↥(fixV (h.projTwo X) ⊓ W₂) = Nat.card W₂ := by
  obtain ⟨e, h1, h2, h3⟩ := h.card_mul_card_fixV_le_aux hb₁ hb₂ hX
  rw [e, h.card_sup] at heq
  set α := Nat.card ↥(X ⊓ P₁)
  set β := Nat.card ↥(fixV X ⊓ W₁)
  set β' := Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁)
  set γδ := Nat.card ↥(h.projTwo X) * Nat.card ↥(fixV (h.projTwo X) ⊓ W₂)
  have hα : 0 < α := Nat.card_pos
  have hW₁ : 0 < Nat.card W₁ := Nat.card_pos
  have hW₂ : 0 < Nat.card W₂ := Nat.card_pos
  have h4 : α * β ≤ α * β' := Nat.mul_le_mul_left _ h1
  have hab : α * β = Nat.card W₁ := by
    by_contra hne
    have hlt : α * β < Nat.card W₁ := lt_of_le_of_ne (h4.trans h2) hne
    have : α * β * γδ < Nat.card W₁ * Nat.card W₂ :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by
        rcases Nat.eq_zero_or_pos γδ with h0 | h0
        · rw [h0, mul_zero] at heq; exact absurd heq.symm (Nat.mul_ne_zero hW₁.ne' hW₂.ne')
        · exact h0)) (Nat.mul_le_mul_left _ h3)
    omega
  have hgd : γδ = Nat.card W₂ := by
    rw [hab] at heq
    exact Nat.eq_of_mul_eq_mul_left hW₁ heq
  have hbb : β = β' := by
    have : α * β' ≤ α * β := hab ▸ h2
    exact le_antisymm h1 (Nat.le_of_mul_le_mul_left this hα)
  exact ⟨hbb ▸ hab, hbb, hgd⟩

theorem projOne_le_of_eq
    (hb₁ : ∀ Y ≤ P₁, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₁) ≤ Nat.card W₁)
    (hb₂ : ∀ Y ≤ P₂, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₂) ≤ Nat.card W₂)
    {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂)
    (heq : Nat.card X * Nat.card ↥(fixV X ⊓ (W₁ ⊔ W₂)) = Nat.card ↥(W₁ ⊔ W₂)) :
    h.projOne X ≤ X ∧ Nat.card ↥(h.projOne X) * Nat.card ↥(fixV (h.projOne X) ⊓ W₁) =
      Nat.card W₁ := by
  have hX' : X ≤ P₂ ⊔ P₁ := sup_comm P₁ P₂ ▸ hX
  obtain ⟨hA, hB, -⟩ := h.eq_of_card_mul_card_fixV_eq hb₁ hb₂ hX heq
  have heq' : Nat.card X * Nat.card ↥(fixV X ⊓ (W₂ ⊔ W₁)) = Nat.card ↥(W₂ ⊔ W₁) := by
    rw [sup_comm W₂ W₁]; exact heq
  obtain ⟨-, -, hC⟩ := h.symm.eq_of_card_mul_card_fixV_eq hb₂ hb₁ hX' heq'
  have hfix := h.symm.fixV_inf_two hX'
  have hle : X ⊓ P₁ ≤ h.projOne X := by
    intro x hx
    rw [ProdSetting.projOne, h.symm.mem_projTwo_iff hX']
    exact ⟨hx.2, 1, P₂.one_mem, by rw [one_mul]; exact hx.1⟩
  have hc1 : Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁) = Nat.card ↥(fixV (h.projOne X) ⊓ W₁) := by
    rw [← hB, hfix]
  have hpos : 0 < Nat.card ↥(fixV (h.projOne X) ⊓ W₁) := Nat.card_pos
  have hcard : Nat.card ↥(X ⊓ P₁) = Nat.card ↥(h.projOne X) := by
    have h5 : Nat.card ↥(X ⊓ P₁) * Nat.card ↥(fixV (h.projOne X) ⊓ W₁) =
        Nat.card ↥(h.projOne X) * Nat.card ↥(fixV (h.projOne X) ⊓ W₁) := by
      calc Nat.card ↥(X ⊓ P₁) * Nat.card ↥(fixV (h.projOne X) ⊓ W₁)
          = Nat.card ↥(X ⊓ P₁) * Nat.card ↥(fixV (X ⊓ P₁) ⊓ W₁) := by rw [hc1]
        _ = Nat.card ↥W₁ := hA
        _ = _ := hC.symm
    exact Nat.eq_of_mul_eq_mul_right hpos h5
  have heqX : X ⊓ P₁ = h.projOne X := Subgroup.eq_of_le_of_card_ge hle hcard.symm.le
  exact ⟨heqX ▸ inf_le_left, hC⟩

end ProdSetting

end CFSG.Quasithin.Vol2.Ch10.SecE
