module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Fan86.Sym3

open Equiv

theorem card_perm : Nat.card (Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem sq_or_cube : ∀ g : Perm (Fin 3), g ≠ 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

theorem exists_noncomm : ∀ g : Perm (Fin 3), g ≠ 1 → g ^ 2 = 1 → ∃ h : Perm (Fin 3),
    h * g * h⁻¹ ≠ g := by decide

theorem mul_cube : ∀ g g' : Perm (Fin 3), g ≠ 1 → g ^ 2 = 1 → g' ≠ 1 → g' ^ 2 = 1 → g ≠ g' →
    (g * g') ^ 3 = 1 ∧ g * g' ≠ 1 := by decide

theorem eq_one_of_cube {g : Perm (Fin 3)} {m : ℕ} (h2 : g ^ (2 ^ m) = 1) (h3 : g ^ 3 = 1) :
    g = 1 := by
  have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
  have := pow_gcd_eq_one.2 ⟨h2, h3⟩
  rwa [hcop, pow_one] at this

theorem eq_bot_of_normal_isPGroup (N : Subgroup (Perm (Fin 3))) [N.Normal] (hN : IsPGroup 2 N) :
    N = ⊥ := by
  by_contra hne
  obtain ⟨g, hgN, hg1⟩ : ∃ g ∈ N, g ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_bot_iff_forall N |>.2 h)
  have hsq : ∀ g ∈ N, g ≠ 1 → g ^ 2 = 1 := by
    intro g hg hg1
    rcases sq_or_cube g hg1 with h | h
    · exact h
    · obtain ⟨m, hm⟩ := hN ⟨g, hg⟩
      exact absurd (eq_one_of_cube (congrArg Subtype.val hm) h) hg1
  have hg2 := hsq g hgN hg1
  obtain ⟨h, hh⟩ := exists_noncomm g hg1 hg2
  have hg'N : h * g * h⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance g hgN h
  have hg'1 : h * g * h⁻¹ ≠ 1 := by
    intro h1
    apply hg1
    calc g = h⁻¹ * (h * g * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  have hg'2 := hsq _ hg'N hg'1
  obtain ⟨hc, hc1⟩ := mul_cube g (h * g * h⁻¹) hg1 hg2 hg'1 hg'2 (Ne.symm hh)
  obtain ⟨m, hm⟩ := hN ⟨g * (h * g * h⁻¹), N.mul_mem hgN hg'N⟩
  exact hc1 (eq_one_of_cube (congrArg Subtype.val hm) hc)

theorem eq_top_of_dvd (R : Subgroup (Perm (Fin 3))) (h2 : 2 ∣ Nat.card R) (h3 : 3 ∣ Nat.card R) :
    R = ⊤ := by
  have h6 : 6 ∣ Nat.card R := by
    have : Nat.Coprime 2 3 := by norm_num
    simpa using this.mul_dvd_of_dvd_of_dvd h2 h3
  have hd : Nat.card R ∣ 6 := card_perm ▸ Subgroup.card_subgroup_dvd_card R
  have h : Nat.card R = 6 := Nat.dvd_antisymm hd h6
  exact Subgroup.eq_top_of_card_eq R (by rw [h, card_perm])

end CFSG.Quasithin.Fan86.Sym3
