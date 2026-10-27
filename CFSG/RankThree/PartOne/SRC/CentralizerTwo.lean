module

public import CFSG.RankThree.PartOne.SRC.ProductCover

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup

theorem rankFourCover_of_two_SL2_gen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hX : ∀ (W : Type) [Group W] [Finite W]
      (ρ : W →* Matrix.SpecialLinearGroup (Fin 2) F₁ × Matrix.SpecialLinearGroup (Fin 2) F₂),
      Function.Surjective ρ → IsPGroup p ρ.ker →
        ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k)
    {S : Type} [Group S]
    (ι₁ : Matrix.SpecialLinearGroup (Fin 2) F₁ →* S)
    (ι₂ : Matrix.SpecialLinearGroup (Fin 2) F₂ →* S) (hι₁ : Function.Injective ι₁)
    (hι₂ : Function.Injective ι₂) (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) {t : S}
    (ht : orderOf t = 2) (hc₁ : ∀ a, ι₁ a * t = t * ι₁ a) (hc₂ : ∀ b, ι₂ b * t = t * ι₂ b) :
    RankFourCover p S := by
  let ι : Matrix.SpecialLinearGroup (Fin 2) F₁ × Matrix.SpecialLinearGroup (Fin 2) F₂ →* S :=
    ι₁.noncommCoprod ι₂ fun a b => hcomm a b
  have hι : ∀ x, ι x = ι₁ x.1 * ι₂ x.2 := fun x => rfl
  refine rankFourCover_of_cover_ker hp hp2 hX ι ?_ ht ?_
  · rintro ⟨a, b⟩ h
    have h' : ι₁ a * ι₂ b = 1 := h
    have hmul : ι₁ a = (ι₂ b)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hmul' : ι₂ b = (ι₁ a)⁻¹ := eq_inv_of_mul_eq_one_right h'
    have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₁) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hι₁
      rw [map_mul, map_mul, hmul]
      exact ((show Commute (ι₁ g) (ι₂ b) from hcomm g b).inv_right).eq
    have hb : b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₂) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hι₂
      rw [map_mul, map_mul, hmul']
      exact ((show Commute (ι₂ g) (ι₁ a) from (hcomm a g).symm).inv_right).eq
    exact Prod.ext (sq_eq_one_of_mem_center_SL2 ha) (sq_eq_one_of_mem_center_SL2 hb)
  · rintro ⟨a, b⟩
    show ι₁ a * ι₂ b * t = t * (ι₁ a * ι₂ b)
    calc ι₁ a * ι₂ b * t = ι₁ a * (ι₂ b * t) := by rw [mul_assoc]
      _ = ι₁ a * (t * ι₂ b) := by rw [hc₂]
      _ = (ι₁ a * t) * ι₂ b := by rw [mul_assoc]
      _ = (t * ι₁ a) * ι₂ b := by rw [hc₁]
      _ = t * (ι₁ a * ι₂ b) := by rw [mul_assoc]


theorem rankFourCover_of_two_SL2 {p e₁ e₂ : ℕ} [Fact p.Prime] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] [CharP F₁ p] [CharP F₂ p] (hF₁ : Nat.card F₁ = p ^ e₁)
    (hF₂ : Nat.card F₂ = p ^ e₂) (hp2 : p ≠ 2) (he₁ : 2 ≤ e₁) (he₂ : 2 ≤ e₂)
    (h₁9 : Nat.card F₁ ≠ 9) (h₂9 : Nat.card F₂ ≠ 9) {S : Type} [Group S]
    (ι₁ : Matrix.SpecialLinearGroup (Fin 2) F₁ →* S)
    (ι₂ : Matrix.SpecialLinearGroup (Fin 2) F₂ →* S) (hι₁ : Function.Injective ι₁)
    (hι₂ : Function.Injective ι₂) (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) {t : S}
    (ht : orderOf t = 2) (hc₁ : ∀ a, ι₁ a * t = t * ι₁ a) (hc₂ : ∀ b, ι₂ b * t = t * ι₂ b) :
    RankFourCover p S :=
  rankFourCover_of_two_SL2_gen (Fact.out : p.Prime) hp2
    (fun _ _ _ ρ hρ hk => rank_four_of_cover_SL2_prod hF₁ hF₂ hp2 he₁ he₂ h₁9 h₂9 ρ hρ hk)
    ι₁ ι₂ hι₁ hι₂ hcomm ht hc₁ hc₂

end CFSG.RankThree.PartOne.SRC
