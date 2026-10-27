module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Base

public section

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] (a : ℕ)

@[expose] def perp (T : Set F) : Set F := {c | ∀ d ∈ T, d * sg a c = sg a d * c}

omit [Finite F] in
theorem sg_ne_zero {w : F} (hw : w ≠ 0) : sg a w ≠ 0 := by
  rw [sg_apply]; exact pow_ne_zero _ hw

omit [Finite F] in
theorem div_mem_Kf {c w : F} (hw : w ≠ 0)
    (h : sg a c * w = c * sg a w) : c / w ∈ (Kf a : Subfield F) := by
  rw [mem_Kf, map_div₀, div_eq_div_iff (sg_ne_zero a hw) hw]
  exact h

theorem card_Kf_pos : 0 < Nat.card ((Kf a : Subfield F) : Set F) :=
  Nat.card_pos_iff.mpr ⟨⟨⟨0, (Kf a).zero_mem⟩⟩, inferInstance⟩

theorem card_perp_single_le {w : F} (hw : w ≠ 0) :
    Nat.card (perp a {w}) ≤ Nat.card ((Kf a : Subfield F) : Set F) := by
  by_cases hP : ∃ c₀ ∈ perp a {w}, c₀ ≠ 0
  · obtain ⟨c₀, hc₀, hc₀0⟩ := hP
    have hc₀' : w * sg a c₀ = sg a w * c₀ := hc₀ w rfl
    have hmem : ∀ c ∈ perp a {w}, c / c₀ ∈ (Kf a : Subfield F) := by
      intro c hc
      have hc' : w * sg a c = sg a w * c := hc w rfl
      apply div_mem_Kf a hc₀0
      have hsw := sg_ne_zero a hw
      apply mul_right_cancel₀ (mul_ne_zero hw hsw)
      linear_combination (c₀ * sg a w) * hc' - (c * sg a w) * hc₀'
    refine Nat.card_le_card_of_injective
      (fun c => (⟨c.1 / c₀, hmem c.1 c.2⟩ : ((Kf a : Subfield F) : Set F))) ?_
    intro c c' hcc
    have := congrArg Subtype.val hcc
    exact Subtype.ext ((div_left_inj' hc₀0).mp this)
  · push Not at hP
    have hsub : perp a {w} ⊆ {0} := fun c hc => hP c hc
    calc Nat.card (perp a {w}) ≤ Nat.card ({0} : Set F) :=
          Nat.card_mono (Set.finite_singleton _) hsub
      _ = 1 := Nat.card_unique
      _ ≤ _ := card_Kf_pos a

theorem card_mul_card_perp_le (ha : 0 < a) (hF : Nat.card F = 2 ^ (2 * a)) (T : Set F) {w : F}
    (hwT : w ∈ T) (hw : w ≠ 0) : Nat.card T * Nat.card (perp a T) ≤ Nat.card F := by
  have hsw := sg_ne_zero a hw
  by_cases hcase : ∀ d ∈ T, sg a d * w = d * sg a w
  · have h1 : Nat.card T ≤ Nat.card ((Kf a : Subfield F) : Set F) := by
      refine Nat.card_le_card_of_injective
        (fun d => (⟨d.1 / w, div_mem_Kf a hw (hcase d.1 d.2)⟩ :
          ((Kf a : Subfield F) : Set F))) ?_
      intro d d' hdd
      exact Subtype.ext ((div_left_inj' hw).mp (congrArg Subtype.val hdd))
    have h2 : Nat.card (perp a T) ≤ Nat.card ((Kf a : Subfield F) : Set F) :=
      (Nat.card_mono (Set.toFinite _) (fun c hc d hd => by
        rw [Set.mem_singleton_iff.mp hd]; exact hc w hwT : perp a T ⊆ perp a {w})).trans
        (card_perp_single_le a hw)
    have h3 := card_Kf a ha hF
    calc Nat.card T * Nat.card (perp a T)
        ≤ Nat.card ((Kf a : Subfield F) : Set F) * Nat.card ((Kf a : Subfield F) : Set F) :=
          Nat.mul_le_mul h1 h2
      _ = Nat.card F := by rw [h3, hF, ← pow_add, two_mul]
  · push Not at hcase
    obtain ⟨d', hd'T, hd'⟩ := hcase
    have hsub : perp a T ⊆ {0} := by
      intro c hc
      by_contra hc0
      have e1 := hc d' hd'T
      have e2 := hc w hwT
      have : (sg a d' * w - d' * sg a w) * c = 0 := by
        linear_combination (-w) * e1 + d' * e2
      rcases mul_eq_zero.mp this with h | h
      · exact hd' (sub_eq_zero.mp h)
      · exact hc0 h
    have h1 : Nat.card (perp a T) ≤ 1 :=
      (Nat.card_mono (Set.finite_singleton _) hsub).trans (Nat.card_unique.le)
    have h2 : Nat.card T ≤ Nat.card F :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    calc Nat.card T * Nat.card (perp a T) ≤ Nat.card F * 1 := Nat.mul_le_mul h2 h1
      _ = Nat.card F := mul_one _

end CFSG.Quasithin.H11
