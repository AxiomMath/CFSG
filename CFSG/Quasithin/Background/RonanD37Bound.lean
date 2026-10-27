module

public import CFSG.Quasithin.Background.RonanD37Swap
public import CFSG.Quasithin.Background.RonanD37Norm

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37

variable {U : Type} [CommGroup U] [Finite U] {X L₁ L₂ : Subgroup (MulAut U)} {s : MulAut U}
  {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem one_le_rk_iff {H : Subgroup (MulAut U)} (hH : IsPGroup 2 ↥H) : 1 ≤ rk H ↔ H ≠ ⊥ := by
  constructor
  · intro h1 hbot
    rw [(rk_eq_zero_iff_of_isPGroup hH).mpr hbot] at h1
    omega
  · intro hne
    rcases Nat.eq_zero_or_pos (rk H) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hH).mp h) hne
    · exact h

theorem swap_two
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 2) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (hL : IsPSL 2 2 n ↥L₁) {B : Subgroup (MulAut U)}
    (hB : IsA2 X B) {b : MulAut U} (hbB : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    (3 * rk B ≤ 2 * rkIdx (fixV B) ∧
        (3 * rk B = 2 * rkIdx (fixV B) → rk B = 2 * n ∨ (n = 3 ∧ rk B = 4))) ∨
      (n = 2 ∧ 3 * rkIdx (fixV B) = 4 * rk B ∧ rk B = 3) := by
  have hE := hB.2.2
  have hb : b * b = 1 := by rw [← pow_two]; exact hE.2 b hbB
  obtain ⟨ht₁, ht₂⟩ := hC.swap_of_not_mem (hB.1 hbB) hbN
  set B₀ := B ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) with hB₀def
  have hcardB := hC.card_eq_two_mul hB.1 hbB hbN
  have hE₀ : IsElemAbelian2 B₀ :=
    ⟨fun x hx y hy => hE.1 x hx.1 y hy.1, fun x hx => hE.2 x hx.1⟩
  have hPN₀ : ∀ a ∈ B₀, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer ha.2 hl
  have hrk₀ := card_le_mul_cent_psl Mm (by norm_num) hC.simple (Mm.not_comm le_rfl) hC.sqtk hL
    hE₀ hPN₀
  rw [norm_inf_cent_eq_bot Mm hE hbB ht₂, Subgroup.card_bot, mul_one] at hrk₀
  have hU := natCard_eq_of_matModel Mm
  have hsw := card_fixV_swap_le Mm b hb ht₁ ht₂
  rw [show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl, pow_one] at hsw
  have hle : fixV B ≤ fixV (Subgroup.zpowers b) := fixV_anti (Subgroup.zpowers_le.mpr hbB)
  have hsw' : Nat.card F * Nat.card ↥(fixV B) ≤ Nat.card U :=
    (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)).trans hsw
  have h2n : B₀ ≠ ⊥ → Nat.card F ^ 2 * Nat.card ↥(fixV B) ≤ Nat.card U :=
    card_fixV_le_swap_two hC Mm hB hbB hbN
  have hB2 : IsPGroup 2 ↥B := hE.isPGroup
  have hcB := card_eq_two_pow_of_isPGroup hB2
  have hcB₀ := card_eq_two_pow_of_isPGroup (hB2.to_le (inf_le_left : B₀ ≤ B))
  have hcf := card_fixV_eq hC.exp B
  have hidx := rk_add_rkIdx (fixV B)
  rw [rk_top_eq Mm hF] at hidx
  have ha := (one_le_rk_iff hB2).mpr hB.2.1
  rw [hU, hF] at hsw'
  rw [hcB, hcB₀] at hcardB
  rw [hcB₀] at hrk₀
  set a := rk B
  set a₀ := rk ↥B₀
  set f := rk ↥(fixV B)
  have e1 : a = a₀ + 1 := by
    apply Nat.pow_right_injective (le_refl 2)
    simp only
    rw [hcardB, pow_succ, mul_comm]
  have e2 : a₀ ≤ n := le_of_two_pow_le hrk₀
  have e3 : n + f ≤ 2 * 2 * n := by
    apply le_of_two_pow_le
    rw [hcf] at hsw'
    calc 2 ^ (n + f) = 2 ^ n * 2 ^ f := by ring
      _ ≤ (2 ^ n) ^ (2 * 2) := hsw'
      _ = 2 ^ (2 * 2 * n) := by ring
  have e4 : 1 ≤ a₀ → 2 * n + f ≤ 2 * 2 * n := by
    intro h1
    have h := h2n ((one_le_rk_iff (hB2.to_le (inf_le_left : B₀ ≤ B))).mp h1)
    rw [hU, hF, hcf] at h
    apply le_of_two_pow_le
    calc 2 ^ (2 * n + f) = (2 ^ n) ^ 2 * 2 ^ f := by ring
      _ ≤ (2 ^ n) ^ (2 * 2) := h
      _ = 2 ^ (2 * 2 * n) := by ring
  rcases Nat.eq_zero_or_pos a₀ with h0 | h0
  · left
    omega
  · have := e4 h0
    by_cases hn3 : 3 ≤ n
    · left
      constructor
      · omega
      · intro heq
        right
        omega
    · have hn2 : n = 2 := by omega
      by_cases h5 : a = 3 ∧ rkIdx (fixV B) = 4
      · right
        omega
      · left
        omega

theorem swap_three (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 3) (hF : Nat.card F = 2)
    {B : Subgroup (MulAut U)} (hB : IsA2 X B) {b : MulAut U} (hbB : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    5 * rk B ≤ 4 * rkIdx (fixV B) ∧ (5 * rk B = 4 * rkIdx (fixV B) → rk B = 4) := by
  have hE := hB.2.2
  have hb : b * b = 1 := by rw [← pow_two]; exact hE.2 b hbB
  obtain ⟨ht₁, ht₂⟩ := hC.swap_of_not_mem (hB.1 hbB) hbN
  set B₀ := B ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) with hB₀def
  have hcardB := hC.card_eq_two_mul hB.1 hbB hbN
  have hE₀ : IsElemAbelian2 B₀ :=
    ⟨fun x hx y hy => hE.1 x hx.1 y hy.1, fun x hx => hE.2 x hx.1⟩
  have hPN₀ : ∀ a ∈ B₀, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer ha.2 hl
  have h8 : Nat.card F ^ 3 = 8 := by rw [hF]; norm_num
  have hrk₀ := card_le_mul_cent_eight Mm (by norm_num) h8 hE₀ hPN₀
  rw [norm_inf_cent_eq_bot Mm hE hbB ht₂, Subgroup.card_bot, mul_one] at hrk₀
  have hU := natCard_eq_of_matModel Mm
  have hsw := card_fixV_swap_le Mm b hb ht₁ ht₂
  rw [show (3 * (3 - 1) / 2 : ℕ) = 3 from rfl, hU, hF] at hsw
  have hle : fixV B ≤ fixV (Subgroup.zpowers b) := fixV_anti (Subgroup.zpowers_le.mpr hbB)
  have hstrict : B₀ ≠ ⊥ → 2 * Nat.card ↥(fixV B) ≤ Nat.card ↥(fixV (Subgroup.zpowers b)) :=
    two_mul_card_fixV_le_swap hC Mm (by norm_num) hB hbB hbN
  have hB2 : IsPGroup 2 ↥B := hE.isPGroup
  have hcB := card_eq_two_pow_of_isPGroup hB2
  have hcB₀ := card_eq_two_pow_of_isPGroup (hB2.to_le (inf_le_left : B₀ ≤ B))
  have hcf := card_fixV_eq hC.exp B
  have hcg := card_fixV_eq hC.exp (Subgroup.zpowers b)
  have hidx := rk_add_rkIdx (fixV B)
  rw [rk_top_eq Mm (n := 1) (by rw [hF, pow_one])] at hidx
  have ha := (one_le_rk_iff hB2).mpr hB.2.1
  rw [hcB, hcB₀] at hcardB
  rw [hcB₀] at hrk₀
  rw [hcg] at hsw
  have hfg : rk ↥(fixV B) ≤ rk ↥(fixV (Subgroup.zpowers b)) := rk_mono hle
  set a := rk B
  set a₀ := rk ↥B₀
  set f := rk ↥(fixV B)
  set g := rk ↥(fixV (Subgroup.zpowers b))
  have e1 : a = a₀ + 1 := by
    apply Nat.pow_right_injective (le_refl 2)
    simp only
    rw [hcardB, pow_succ, mul_comm]
  have e2 : a₀ ≤ 2 := by
    apply le_of_two_pow_le
    calc 2 ^ a₀ ≤ 4 := hrk₀
      _ = 2 ^ 2 := by norm_num
  have e3 : 3 + g ≤ 9 := by
    apply le_of_two_pow_le
    calc 2 ^ (3 + g) = 2 ^ 3 * 2 ^ g := by ring
      _ ≤ 2 ^ (3 * 3) := hsw
      _ = 2 ^ 9 := by norm_num
  have e4 : 1 ≤ a₀ → f + 1 ≤ g := by
    intro h1
    have h := hstrict ((one_le_rk_iff (hB2.to_le (inf_le_left : B₀ ≤ B))).mp h1)
    rw [hcf, hcg] at h
    apply le_of_two_pow_le
    calc 2 ^ (f + 1) = 2 * 2 ^ f := by ring
      _ ≤ 2 ^ g := h
  rcases Nat.eq_zero_or_pos a₀ with h0 | h0
  · omega
  · have := e4 h0
    omega

theorem bound_two
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 2) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (hL : IsPSL 2 2 n ↥L₁) {B : Subgroup (MulAut U)}
    (hB : IsA2 X B) :
    (3 * rk B ≤ 2 * rkIdx (fixV B) ∧
        (3 * rk B = 2 * rkIdx (fixV B) → rk B = 2 * n ∨ (n = 3 ∧ rk B = 4))) ∨
      (n = 2 ∧ 3 * rkIdx (fixV B) = 4 * rk B ∧ rk B = 3) := by
  by_cases hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (L₁ : Set (MulAut U))
  · obtain ⟨h1, h2⟩ := norm_two hC Mm hF hL hB hN
    exact Or.inl ⟨h1, fun h => Or.inl (h2 h)⟩
  · push Not at hN
    obtain ⟨b, hbB, hbN⟩ := hN
    exact swap_two hC Mm hF hn hL hB hbB hbN

theorem bound_three (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 3) (hF : Nat.card F = 2)
    {B : Subgroup (MulAut U)} (hB : IsA2 X B) :
    5 * rk B ≤ 4 * rkIdx (fixV B) ∧ (5 * rk B = 4 * rkIdx (fixV B) → rk B = 4) := by
  by_cases hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (L₁ : Set (MulAut U))
  · exact norm_three hC Mm hF hB hN
  · push Not at hN
    obtain ⟨b, hbB, hbN⟩ := hN
    exact swap_three hC Mm hF hB hbB hbN

end CFSG.Quasithin.RonanD37
