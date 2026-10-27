module

public import CFSG.Quasithin.EmptyFaithful.S153E57B

public section

namespace CFSG.Quasithin

namespace S153E57

open scoped commutatorElement

variable {Q : Type*} [CommGroup Q]

theorem card_eq_of_irr_compl [Finite Q] {K H : Subgroup (MulAut Q)} (hH : IsIrrOn153 H ⊤)
    (hKH : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) {W₁ W₂ : Subgroup Q} (h₁ : IsIrrOn153 K W₁)
    (h₂ : IsIrrOn153 K W₂) (hdis : W₁ ⊓ W₂ = ⊥) (hsup : W₁ ⊔ W₂ = ⊤) :
    Nat.card W₁ = Nat.card W₂ := by
  by_contra hne
  have hcard : Nat.card ↥(W₁ ⊔ W₂) = Nat.card W₁ * Nat.card W₂ := card_sup_of_inf_eq_bot hdis
  have hQ : Nat.card Q = Nat.card W₁ * Nat.card W₂ := by
    rw [← hcard, hsup, Subgroup.card_top]
  have hpos₁ : 0 < Nat.card W₁ := Nat.card_pos
  have hinv : IsInv H W₁ := by
    intro h hh x hx
    set W' := W₁.map (h : Q →* Q) with hW'
    have hW'irr : IsIrrOn153 K W' := isIrr_map hKH hh h₁
    have hW'card : Nat.card W' = Nat.card W₁ := card_map_eq h W₁
    have hinf₂ : IsInv K (W' ⊓ W₂) := (irr_inv hW'irr).inf (irr_inv h₂)
    have hinf₁ : IsInv K (W' ⊓ W₁) := (irr_inv hW'irr).inf (irr_inv h₁)
    by_cases hA : W' ⊓ W₂ = ⊥
    · by_cases hB : W' ⊓ W₁ = ⊥
      ·
        have hX : W' ⊔ W₁ = ⊤ := by
          have hXinv : IsInv K (W' ⊔ W₁) := (irr_inv hW'irr).sup (irr_inv h₁)
          have hmod : (W₁ ⊔ W₂) ⊓ (W' ⊔ W₁) = W₁ ⊔ W₂ ⊓ (W' ⊔ W₁) :=
            sup_inf_assoc_of_le W₂ (le_sup_right : W₁ ≤ W' ⊔ W₁)
          rcases h₂.2.2 (W₂ ⊓ (W' ⊔ W₁)) inf_le_left ((irr_inv h₂).inf hXinv) with h | h
          · exfalso
            rw [hsup, top_inf_eq, h, sup_bot_eq] at hmod
            have hle : W' ≤ W₁ := hmod ▸ (le_sup_left : W' ≤ W' ⊔ W₁)
            have : W' ⊓ W₁ = W' := inf_eq_left.2 hle
            rw [this] at hB
            exact hW'irr.1 hB
          · have : W₂ ≤ W' ⊔ W₁ := h ▸ inf_le_right
            rw [eq_top_iff, ← hsup]
            exact sup_le le_sup_right this
        have h1 : Nat.card ↥(W' ⊔ W₁) = Nat.card W' * Nat.card W₁ := card_sup_of_inf_eq_bot hB
        rw [hX, Subgroup.card_top, hQ, hW'card] at h1
        have : Nat.card W₁ * Nat.card W₂ = Nat.card W₁ * Nat.card W₁ := by rw [h1]
        exact absurd (Nat.eq_of_mul_eq_mul_left hpos₁ this).symm hne
      ·
        have heq : W' = W₁ := by
          have hle : W' ⊓ W₁ ≤ W₁ := inf_le_right
          rcases h₁.2.2 _ hle hinf₁ with h | h
          · exact absurd h hB
          · rcases hW'irr.2.2 _ inf_le_left hinf₁ with h' | h'
            · exact absurd h' hB
            · rw [← h', h]
        rw [← heq]
        exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    · exfalso
      have heq : W' = W₂ := by
        rcases h₂.2.2 _ inf_le_right hinf₂ with h | h
        · exact absurd h hA
        · rcases hW'irr.2.2 _ inf_le_left hinf₂ with h' | h'
          · exact absurd h' hA
          · rw [← h', h]
      apply hne
      rw [← hW'card, heq]
  rcases hH.2.2 W₁ le_top hinv with h | h
  · exact h₁.1 h
  · have : W₂ = ⊥ := by
      rw [← hdis, h, top_inf_eq]
    exact h₂.1 this

namespace Core

variable {H K V P₁ P₂ : Subgroup (MulAut Q)} {v : MulAut Q} {z₀ : Q}
  (hC : Core H K V P₁ P₂ v z₀)

section Fin

variable [Finite Q]

include hC

theorem dichotomy (s : ℕ) (hQ : Nat.card Q = 2 ^ (2 * (s + 2))) :
    IsIrrOn153 K ⊤ ∨ ∃ W₁ W₂ : Subgroup Q, IsIrrOn153 K W₁ ∧ IsIrrOn153 K W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧
      W₁ ⊓ W₂ = ⊥ ∧ Nat.card W₁ = 2 ^ (s + 2) ∧ Nat.card W₂ = 2 ^ (s + 2) ∧
      (∀ w ∈ V, ∀ x ∈ W₁, w x ∈ W₁) ∧ (∀ w ∈ V, ∀ x ∈ W₂, w x ∈ W₂) ∧
      Nat.card ↥(commIn153 V W₁) = 2 ∧ Nat.card ↥(commIn153 V W₂) = 2 := by
  have := hC.nontriv
  obtain ⟨J, -, hJ⟩ := exists_irr_le (K := K) (isInv_top K) top_ne_bot
  by_cases hJtop : J = ⊤
  · left
    rw [← hJtop]
    exact hJ
  · right
    obtain ⟨C, hCinv, hJC, hJCt⟩ := exists_compl hC.hsum (irr_inv hJ)
    have hCne : C ≠ ⊥ := by
      intro h
      rw [h, sup_bot_eq] at hJCt
      exact hJtop hJCt
    have hJstab := hC.v_stable_inv (irr_inv hJ)
    have hCstab := hC.v_stable_inv hCinv
    have hJ2 : 2 ≤ Nat.card ↥(J.map (phi v)) := hC.two_le_card_map (irr_inv hJ) hJ.1
    have hC2 : 2 ≤ Nat.card ↥(C.map (phi v)) := hC.two_le_card_map hCinv hCne
    have hprod : Nat.card ↥(J.map (phi v)) * Nat.card ↥(C.map (phi v)) ≤ 4 := by
      rw [← card_map_phi_sup hJstab hCstab hJC, hJCt, ← hC.comm_eq_map]
      exact hC.comm_le
    have hJc : Nat.card ↥(J.map (phi v)) = 2 := by nlinarith
    have hCc : Nat.card ↥(C.map (phi v)) = 2 := by nlinarith
    have hCirr : IsIrrOn153 K C := by
      refine ⟨hCne, hCinv, fun B' hB'le hB'inv => ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨hB'ne, hB'C⟩ := hcon
      obtain ⟨B'', hB''inv, hB''dis, hB''sup⟩ := exists_compl hC.hsum hB'inv
      have hC₂inv : IsInv K (C ⊓ B'') := hCinv.inf hB''inv
      have hCeq : C = B' ⊔ C ⊓ B'' := by
        have h1 : (B' ⊔ B'') ⊓ C = B' ⊔ B'' ⊓ C := sup_inf_assoc_of_le B'' hB'le
        rw [hB''sup, top_inf_eq, inf_comm B'' C] at h1
        exact h1
      have hC₂ne : C ⊓ B'' ≠ ⊥ := by
        intro h
        rw [h, sup_bot_eq] at hCeq
        exact hB'C hCeq.symm
      have hB'dis : B' ⊓ (C ⊓ B'') = ⊥ := by
        rw [eq_bot_iff, ← hB''dis]
        exact inf_le_inf le_rfl inf_le_right
      have hB'stab := hC.v_stable_inv hB'inv
      have hC₂stab := hC.v_stable_inv hC₂inv
      have h1 : Nat.card ↥(C.map (phi v)) =
          Nat.card ↥(B'.map (phi v)) * Nat.card ↥((C ⊓ B'').map (phi v)) := by
        conv_lhs => rw [hCeq]
        exact card_map_phi_sup hB'stab hC₂stab hB'dis
      have h2 := hC.two_le_card_map hB'inv hB'ne
      have h3 := hC.two_le_card_map hC₂inv hC₂ne
      nlinarith
    have hcard := card_eq_of_irr_compl hC.irr_H hC.normal hJ hCirr hJC hJCt
    have hmul : Nat.card J * Nat.card C = Nat.card Q := by
      rw [← card_sup_of_inf_eq_bot hJC, hJCt, Subgroup.card_top]
    rw [← hcard, hQ] at hmul
    have hsq : Nat.card J ^ 2 = (2 ^ (s + 2)) ^ 2 := by
      rw [pow_two, hmul, ← pow_mul, mul_comm]
    have hJcard : Nat.card J = 2 ^ (s + 2) := Nat.pow_left_injective (by norm_num) hsq
    refine ⟨J, C, hJ, hCirr, hJCt, hJC, hJcard, hcard ▸ hJcard, ?_, ?_, ?_, ?_⟩
    · intro w hw x hx
      rcases hC.V_two w hw with rfl | rfl
      · rw [MulAut.one_apply]; exact hx
      · exact hJstab x hx
    · intro w hw x hx
      rcases hC.V_two w hw with rfl | rfl
      · rw [MulAut.one_apply]; exact hx
      · exact hCstab x hx
    · rw [commIn153_eq_map hC.v_mem hC.V_two]
      exact hJc
    · rw [commIn153_eq_map hC.v_mem hC.V_two]
      exact hCc

end Fin

end Core

end S153E57

end CFSG.Quasithin
