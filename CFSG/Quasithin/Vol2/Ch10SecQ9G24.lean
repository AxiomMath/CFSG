module

public import CFSG.Quasithin.Vol2.Ch10SecC9S4e
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {L W W' X₀ : Subgroup G}

theorem conj_eq_or_of_case5 (hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a) (hirr : IrrG L W)
    (hirr' : IrrG L W') (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLW' : L ≤ Subgroup.normalizer (W' : Set G)) (hni : ¬ IsXSectionIso L ⊥ W W')
    (hcard : Nat.card W = Nat.card W') (hX₀ : X₀ = W ∨ X₀ = W') {u : G}
    (huL : u ∈ Subgroup.normalizer (L : Set G))
    (huV : u ∈ Subgroup.normalizer ((W ⊔ W' : Subgroup G) : Set G)) :
    CFSG.conjugate X₀ u⁻¹ = W ∨ CFSG.conjugate X₀ u⁻¹ = W' := by
  have huL' : u⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ huL
  have hirrX₀ : IrrG L X₀ := by rcases hX₀ with rfl | rfl <;> assumption
  have hLX₀ : L ≤ Subgroup.normalizer (X₀ : Set G) := by rcases hX₀ with rfl | rfl <;> assumption
  have hcX₀ : Nat.card X₀ = Nat.card W := by rcases hX₀ with rfl | rfl; rfl; exact hcard.symm
  set X := CFSG.conjugate X₀ u⁻¹ with hX
  have hirrX : IrrG L X := irrG_conjugate hirrX₀ huL'
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := le_normalizer_conjugate_of' huL' hLX₀
  have hXs : X ≤ W ⊔ W' := by
    intro x hx
    rw [hX, SecA.mem_conjugate_iff, inv_inv] at hx
    have h1 : u⁻¹ * x * u ∈ W ⊔ W' := by
      rcases hX₀ with rfl | rfl
      · exact Subgroup.mem_sup_left hx
      · exact Subgroup.mem_sup_right hx
    have := (Subgroup.mem_normalizer_iff.mp huV (u⁻¹ * x * u)).mp h1
    rwa [show u * (u⁻¹ * x * u) * u⁻¹ = x by group] at this
  have hcX : Nat.card X = Nat.card W := by
    rw [hX, ← hcX₀]
    exact Subgroup.card_map_of_injective (MulAut.conj u⁻¹⁻¹).injective
  have hLXW : L ≤ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_inf' (hLX hl) (hLW hl)
  have hLXW' : L ≤ Subgroup.normalizer ((X ⊓ W' : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_inf' (hLX hl) (hLW' hl)
  rcases hirrX.2 _ inf_le_left hLXW with h1 | h1
  · rcases hirrX.2 _ inf_le_left hLXW' with h2 | h2
    · exact absurd (eq_bot_of_disjoint hc hirr hirr' hLW hLW' hni hXs hLX h1 h2) hirrX.1
    · right
      exact Subgroup.eq_of_le_of_card_ge (h2 ▸ inf_le_right) (by rw [hcX, hcard])
  · left
    exact Subgroup.eq_of_le_of_card_ge (h1 ▸ inf_le_right) hcX.ge

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
