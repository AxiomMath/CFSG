module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.Monster.GMS.LeechCoh

variable {G : Type*} [Group G]

private theorem card_le_of_forall_mem (P : Subgroup G) (T : Finset G) (h : ∀ g ∈ P, g ∈ T) :
    Nat.card P ≤ T.card := by
  classical
  calc Nat.card P = (P : Set G).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ (T : Set G).ncard := Set.ncard_le_ncard (fun g hg => by simpa using h g hg) T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T

theorem card_le_eight (P : Subgroup G) (h4 : ∀ g ∈ P, g * g * (g * g) = 1)
    (hu : ∀ s ∈ P, ∀ s' ∈ P, orderOf s = 2 → orderOf s' = 2 → s = s') :
    Nat.card P ≤ 8 := by
  classical
  have hsq1 : ∀ k ∈ P, k * k = 1 → k ≠ 1 → orderOf k = 2 := fun k _ hk hk1 =>
    orderOf_eq_prime (by rwa [pow_two]) hk1
  by_cases hex : ∀ g ∈ P, g * g = 1
  ·
    by_cases hs : ∃ s ∈ P, orderOf s = 2
    · obtain ⟨s, hsP, hs2⟩ := hs
      refine (card_le_of_forall_mem P {1, s} fun g hg => ?_).trans
        (Finset.card_le_two.trans (by omega))
      by_cases hg1 : g = 1
      · simp [hg1]
      · simp [hu g hg s hsP (hsq1 g hg (hex g hg) hg1) hs2]
    · refine (card_le_of_forall_mem P {1} fun g hg => ?_).trans (by simp)
      by_cases hg1 : g = 1
      · simp [hg1]
      · exact absurd ⟨g, hg, hsq1 g hg (hex g hg) hg1⟩ hs
  · push Not at hex
    obtain ⟨g, hgP, hg1⟩ := hex
    set t := g * g with ht_def
    have htP : t ∈ P := P.mul_mem hgP hgP
    have htt : t * t = 1 := h4 g hgP
    have ht1 : t ≠ 1 := hg1
    have ht2 : orderOf t = 2 := hsq1 t htP htt ht1
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hginv : g⁻¹ = g * t := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      calc g * t * g = g * (g * g) * g := rfl
        _ = g * g * (g * g) := by group
        _ = 1 := htt
    have B1 : ∀ k ∈ P, k * k = 1 → k = 1 ∨ k = t := by
      intro k hkP hk
      by_cases hk1 : k = 1
      · exact Or.inl hk1
      · exact Or.inr (hu k hkP t htP (hsq1 k hkP hk hk1) ht2)
    have B2 : ∀ x ∈ P, x * x = 1 ∨ x * x = t := fun x hxP =>
      B1 (x * x) (P.mul_mem hxP hxP) (h4 x hxP)
    have B3 : ∀ x ∈ P, x * t = t * x := by
      intro x hxP
      have hk : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
        calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
          _ = 1 := by rw [htt]; group
      have hkP : x * t * x⁻¹ ∈ P := P.mul_mem (P.mul_mem hxP htP) (P.inv_mem hxP)
      rcases B1 _ hkP hk with h1 | h1
      · exfalso
        apply ht1
        have : t = x⁻¹ * (x * t * x⁻¹) * x := by group
        rw [this, h1]
        group
      · calc x * t = (x * t * x⁻¹) * x := by group
          _ = t * x := by rw [h1]
    have C : ∀ h ∈ P, h * g * h⁻¹ = g ∨ h * g * h⁻¹ = g * t := by
      intro h hhP
      have hgt : g * t = t * g := B3 g hgP
      have hid : h * g * h⁻¹ = (h * g) * (h * g) * g⁻¹ * (h * h)⁻¹ := by group
      rcases B2 (h * g) (P.mul_mem hhP hgP) with hz | hz <;> rcases B2 h hhP with hq | hq
      · right
        rw [hid, hz, hq, hginv]
        simp
      · left
        rw [hid, hz, hq, hginv, htinv]
        simp [mul_assoc, htt]
      · left
        rw [hid, hz, hq, hginv]
        simp only [inv_one, mul_one]
        rw [← mul_assoc, ← hgt, mul_assoc, htt, mul_one]
      · right
        rw [hid, hz, hq, hginv, htinv]
        calc t * (g * t) * t = (t * g) * (t * t) := by group
          _ = t * g := by rw [htt, mul_one]
          _ = g * t := hgt.symm
    have D : ∀ h ∈ P, h * g = g * h → h = 1 ∨ h = g ∨ h = g * g ∨ h = g * g * g := by
      intro h hhP hcomm
      rcases B2 h hhP with hq | hq
      · rcases B1 h hhP hq with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl h1))
      · have hk : (g * h) * (g * h) = 1 := by
          calc (g * h) * (g * h) = g * (h * g) * h := by group
            _ = g * (g * h) * h := by rw [hcomm]
            _ = (g * g) * (h * h) := by group
            _ = 1 := by rw [hq]; exact htt
        rcases B1 (g * h) (P.mul_mem hgP hhP) hk with h1 | h1
        · right; right; right
          have h2 : h = g⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [h2, hginv]
          exact (mul_assoc g g g).symm
        · right; left
          exact mul_left_cancel (h1.trans ht_def)
    have E : ∃ h₁ ∈ P, ∀ h ∈ P, (h = 1 ∨ h = g ∨ h = g * g ∨ h = g * g * g) ∨
        (h₁⁻¹ * h = 1 ∨ h₁⁻¹ * h = g ∨ h₁⁻¹ * h = g * g ∨ h₁⁻¹ * h = g * g * g) := by
      by_cases hall : ∀ h ∈ P, h * g * h⁻¹ = g
      · refine ⟨1, P.one_mem, fun h hhP => Or.inl (D h hhP ?_)⟩
        have h1 := hall h hhP
        calc h * g = (h * g * h⁻¹) * h := by group
          _ = g * h := by rw [h1]
      · push Not at hall
        obtain ⟨h₁, h₁P, h₁ne⟩ := hall
        have h₁t : h₁ * g * h₁⁻¹ = g * t := (C h₁ h₁P).resolve_left h₁ne
        refine ⟨h₁, h₁P, fun h hhP => ?_⟩
        rcases C h hhP with h1 | h1
        · left
          apply D h hhP
          calc h * g = (h * g * h⁻¹) * h := by group
            _ = g * h := by rw [h1]
        · right
          apply D (h₁⁻¹ * h) (P.mul_mem (P.inv_mem h₁P) hhP)
          have e1 : h * g * h⁻¹ = h₁ * g * h₁⁻¹ := h1.trans h₁t.symm
          calc h₁⁻¹ * h * g = h₁⁻¹ * (h * g * h⁻¹) * h := by group
            _ = h₁⁻¹ * (h₁ * g * h₁⁻¹) * h := by rw [e1]
            _ = g * (h₁⁻¹ * h) := by group
    obtain ⟨h₁, h₁P, hE⟩ := E
    set S : Finset G := {1, g, g * g, g * g * g} with hS
    refine (card_le_of_forall_mem P (S ∪ S.image (fun y => h₁ * y)) fun h hhP => ?_).trans ?_
    · rcases hE h hhP with h1 | h1
      · apply Finset.mem_union_left
        simpa [hS] using h1
      · apply Finset.mem_union_right
        rw [Finset.mem_image]
        refine ⟨h₁⁻¹ * h, ?_, by group⟩
        simpa [hS] using h1
    · calc (S ∪ S.image (fun y => h₁ * y)).card ≤ S.card + (S.image (fun y => h₁ * y)).card :=
          Finset.card_union_le _ _
        _ ≤ 4 + 4 := Nat.add_le_add Finset.card_le_four
            (Finset.card_image_le.trans Finset.card_le_four)
        _ = 8 := rfl

end CFSG.Monster.GMS.LeechCoh
