module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreCoord
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem B_le_cen_bb₁ (h : FF84Sec4 b L B K b₁ b₂) : B ≤ Cen (b * b₁) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.2 (comm_of_mem h (mul_mem_B h) hy).eq.symm

theorem isPGroup_B (h : FF84Sec4 b L B K b₁ b₂) : IsPGroup 3 B := fun x =>
  ⟨1, Subtype.ext (by simpa using pow3_of_mem h x.2)⟩

theorem three_elt_centralizes (h : FF84Sec4 b L B K b₁ b₂) {g : G} {k : ℕ}
    (hgD : g ∈ Cen (b * b₁)) (hgN : g ∈ Nor B) (hk : g ^ 3 ^ k = 1) :
    g ∈ CenS B := by
  have hnc : ∀ u ∈ B, g * u * g⁻¹ ∈ B := fun u hu => (Subgroup.mem_normalizer_iff.1 hgN u).1 hu
  have hS : ∀ u ∈ ({b, b₁, b₂} : Set G),
      g * u * g⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) := fun u hu =>
    h.mono.2.2.1 g hgN u hu
  have hxy : (g * b * g⁻¹) * (g * b₁ * g⁻¹) = b * b₁ := by
    have hc : g * (b * b₁) = (b * b₁) * g := Subgroup.mem_centralizer_singleton_iff.1 hgD
    calc (g * b * g⁻¹) * (g * b₁ * g⁻¹) = g * (b * b₁) * g⁻¹ := by group
      _ = (b * b₁) * g * g⁻¹ := by rw [hc]
      _ = b * b₁ := by group
  have hsq : ∀ {u : G}, g * (g * u * g⁻¹) * g⁻¹ = u → Commute g u := by
    intro u hu
    refine commute_of_sq_commute hk ?_
    have : g ^ 2 * u * (g ^ 2)⁻¹ = u := by
      calc g ^ 2 * u * (g ^ 2)⁻¹ = g * (g * u * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = u := hu
    show g ^ 2 * u = u * g ^ 2
    calc g ^ 2 * u = (g ^ 2 * u * (g ^ 2)⁻¹) * g ^ 2 := by group
      _ = u * g ^ 2 := by rw [this]
  have hbc : Commute g b ∧ Commute g b₁ := by
    rcases xy_cases h (hS b (by simp)) (hS b₁ (by simp)) hxy with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨?_, ?_⟩
      · show g * b = b * g
        calc g * b = (g * b * g⁻¹) * g := by group
          _ = b * g := by rw [e1]
      · show g * b₁ = b₁ * g
        calc g * b₁ = (g * b₁ * g⁻¹) * g := by group
          _ = b₁ * g := by rw [e2]
    · exfalso
      have hcb : Commute g b := hsq (by rw [e1, e2])
      have : g * b * g⁻¹ = b := by
        calc g * b * g⁻¹ = b * g * g⁻¹ := by rw [hcb.eq]
          _ = b := by group
      rw [e1] at this
      exact b₁_notin_zpowers_b h (this ▸ Subgroup.mem_zpowers b)
  obtain ⟨hcb, hcb₁⟩ := hbc
  have hb1 : g * b * g⁻¹ = b := by
    calc g * b * g⁻¹ = b * g * g⁻¹ := by rw [hcb.eq]
      _ = b := by group
  have hb11 : g * b₁ * g⁻¹ = b₁ := by
    calc g * b₁ * g⁻¹ = b₁ * g * g⁻¹ := by rw [hcb₁.eq]
      _ = b₁ := by group
  have hcb₂ : Commute g b₂ := by
    have hz := hS b₂ (by simp)
    obtain ⟨a, c, d, hzeq, hcases⟩ := six_coord hz
    have hinj : ∀ w : G, g * w * g⁻¹ = g * b₂ * g⁻¹ → w = b₂ := fun w hw =>
      mul_left_cancel (mul_right_cancel hw)
    rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exfalso
      simp only [zpow_one, zpow_zero, mul_one] at hzeq
      have := hinj b (hb1.trans hzeq.symm)
      exact b₂_notin_zpowers_b h (this ▸ Subgroup.mem_zpowers b)
    · exfalso
      simp only [zpow_neg, zpow_one, zpow_zero, mul_one] at hzeq
      have : g * b⁻¹ * g⁻¹ = g * b₂ * g⁻¹ := by
        calc g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ := by group
          _ = b⁻¹ := by rw [hb1]
          _ = g * b₂ * g⁻¹ := hzeq.symm
      have := hinj b⁻¹ this
      exact b₂_notin_zpowers_b h (this ▸ inv_mem (Subgroup.mem_zpowers b))
    · exfalso
      simp only [zpow_one, zpow_zero, mul_one, one_mul] at hzeq
      have := hinj b₁ (hb11.trans hzeq.symm)
      exact b₂_notin_zpowers_b₁ h (this ▸ Subgroup.mem_zpowers b₁)
    · exfalso
      simp only [zpow_neg, zpow_one, zpow_zero, mul_one, one_mul] at hzeq
      have : g * b₁⁻¹ * g⁻¹ = g * b₂ * g⁻¹ := by
        calc g * b₁⁻¹ * g⁻¹ = (g * b₁ * g⁻¹)⁻¹ := by group
          _ = b₁⁻¹ := by rw [hb11]
          _ = g * b₂ * g⁻¹ := hzeq.symm
      have := hinj b₁⁻¹ this
      exact b₂_notin_zpowers_b₁ h (this ▸ inv_mem (Subgroup.mem_zpowers b₁))
    · simp only [zpow_one, zpow_zero, one_mul] at hzeq
      show g * b₂ = b₂ * g
      calc g * b₂ = (g * b₂ * g⁻¹) * g := by group
        _ = b₂ * g := by rw [hzeq]
    · exfalso
      simp only [zpow_neg, zpow_one, zpow_zero, one_mul] at hzeq
      have hcc : Commute g b₂ := hsq (by
        have : g * b₂ * g⁻¹ = b₂⁻¹ := hzeq
        rw [this]
        calc g * b₂⁻¹ * g⁻¹ = (g * b₂ * g⁻¹)⁻¹ := by group
          _ = b₂ := by rw [this]; simp)
      have h2 : g * b₂ * g⁻¹ = b₂ := by
        calc g * b₂ * g⁻¹ = b₂ * g * g⁻¹ := by rw [hcc.eq]
          _ = b₂ := by group
      have h4 : b₂ = b₂⁻¹ := h2.symm.trans hzeq
      have h3 : b₂ ^ 2 = 1 := by
        calc b₂ ^ 2 = b₂ * b₂ := sq b₂
          _ = b₂ * b₂⁻¹ := by rw [← h4]
          _ = 1 := by simp
      exact absurd (by
        have h33 := pow3_of_mem h (mem_b₂ h)
        calc b₂ = b₂ ^ 3 * (b₂ ^ 2)⁻¹ := by group
          _ = 1 := by rw [h33, h3]; simp) (b₂_ne_one h)
  have hgB : B ≤ Cen g := by
    refine B_le_of_mem' h ?_ ?_ ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcb.eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcb₁.eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcb₂.eq.symm
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hgB hy)

theorem S41_B_sylow (h : FF84Sec4 b L B K b₁ b₂) : IsSylowOf 3 B (Cen (b * b₁)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_of_normalizer (B_le_cen_bb₁ h) (isPGroup_B h) ?_
  rintro g hgD hgN ⟨k, hk⟩
  have hgC := three_elt_centralizes h hgD hgN hk
  have hgb : g ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 (hgC b (mem_b h)).symm
  have hQp : IsPGroup 3 ↥(B ⊔ Subgroup.zpowers g) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_B h) (isPGroup_zpowers hk)
      (Subgroup.zpowers_le.2 hgN)
  have hQle : B ⊔ Subgroup.zpowers g ≤ Cen b :=
    sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_mem h (mem_b h) hy).eq.symm) (Subgroup.zpowers_le.2 hgb)
  exact le_of_isSylowOf h.sylB hQle hQp le_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
