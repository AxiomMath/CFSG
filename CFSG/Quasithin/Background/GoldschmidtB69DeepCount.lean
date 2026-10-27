module

public import CFSG.Quasithin.Background.B69Cnt

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace B69

theorem arith_count {a k k' aY cY c₁ c₂ s₁ s₂ d y : ℕ} (hd : 0 < d) (H1 : y ≤ aY * cY)
    (H2 : k ≤ k') (H3 : aY * k' = a) (H4 : cY ≤ c₁ * c₂ * d) (H5 : y = s₁ * s₂ * d) :
    s₁ * s₂ * k ≤ a * c₁ * c₂ := by
  have h1 : y * k ≤ a * (c₁ * c₂ * d) := by
    calc y * k ≤ aY * cY * k := Nat.mul_le_mul_right _ H1
      _ ≤ aY * cY * k' := Nat.mul_le_mul_left _ H2
      _ = a * cY := by rw [← H3]; ring
      _ ≤ a * (c₁ * c₂ * d) := Nat.mul_le_mul_left _ H4
  have h2 : (s₁ * s₂ * k) * d ≤ (a * c₁ * c₂) * d := by
    calc (s₁ * s₂ * k) * d = y * k := by rw [H5]; ring
      _ ≤ a * (c₁ * c₂ * d) := h1
      _ = (a * c₁ * c₂) * d := by ring
  exact Nat.le_of_mul_le_mul_right h2 hd

variable {V : Type} [CommGroup V] [Finite V]

theorem two_sections_count (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {W₁ W₂ : Subgroup V} (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V)) (hne : W₁ ≠ W₂) :
    Nat.card (Sec W₁ (fixV L)) * Nat.card (Sec W₂ (fixV L)) *
        Nat.card ↥(A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L)) ≤
      Nat.card A * Nat.card ↥(fixV (autSec A W₁ (fixV L))) *
        Nat.card ↥(fixV (autSec A W₂ (fixV L))) := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA h₁
  have hA₂ := a_stab_irr hV hA hL hLA h₂
  have hind := inf_le_fixV_of_ne h₁ h₂ hne
  have hAY : ∀ a ∈ A, ∀ y ∈ W₁ ⊔ W₂, a y ∈ W₁ ⊔ W₂ := isInv_sup hA₁ hA₂
  have hAst : A ≤ stabSub (W₁ ⊔ W₂) := B1.le_stabSub_of_invariant hAY
  have hnt : commSub (W₁ ⊔ W₂) A ≠ ⊥ := fun h =>
    commSub_ne_bot_of_irr hLA h₁ (eq_bot_iff.2 (h ▸ commSub_mono le_sup_left le_rfl))
  obtain ⟨hmin, -⟩ := B1_5_2 hV hA hAY hnt
  have hY1 : Nat.card ↥(W₁ ⊔ W₂) ≤
      Nat.card ↥(autSub A (W₁ ⊔ W₂)) * Nat.card ↥(fixV (autSub A (W₁ ⊔ W₂))) := by
    have h := hmin.1.2.2.2 ⊥ bot_le
    have e : fixV (⊥ : Subgroup (MulAut ↥(W₁ ⊔ W₂))) = ⊤ := eq_top_iff.2 fun v _ x hx => by
      rw [Subgroup.mem_bot.1 hx]
      rfl
    rwa [Subgroup.card_bot, one_mul, e, Subgroup.card_top] at h
  have hK0 : A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L) ≤ A ⊓ centSub (W₁ ⊔ W₂) := by
    intro a ha
    obtain ⟨⟨haA, ha1⟩, ha2⟩ := ha
    refine ⟨haA, ?_⟩
    have e1 := sec_triv_imp_triv hL hAn h₁ hA₁ haA ha1.2
    have e2 := sec_triv_imp_triv hL hAn h₂ hA₂ haA ha2.2
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul, e1 x hx, e2 z hz]
  have hk' := Subgroup.card_le_of_le hK0
  have hA3 := card_autSub_mul hAst
  exact arith_count Nat.card_pos hY1 hk' hA3 (card_fixY_le (fixV L) hind hA₁ hA₂)
    (card_Y_eq (fixV L) hind)

omit [Finite V] in
theorem not_le_centSec_of_irr {A L : Subgroup (MulAut V)} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hWA : ∀ b ∈ A, ∀ w ∈ W, b w ∈ W) :
    ¬ A ≤ centSec W (fixV L) := by
  intro hle
  apply commSub_ne_bot_of_irr hLA hW
  rw [commSub_eq_bot_iff]
  intro w hw a ha
  exact sec_triv_imp_triv hL hAn hW hWA ha (hle ha).2 w hw

end B69

end CFSG.Quasithin
