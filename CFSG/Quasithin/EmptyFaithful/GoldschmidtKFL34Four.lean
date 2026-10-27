module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.SBd19F

variable {G : Type*} [Group G]

theorem exists_commutator_eq {U : Subgroup G} (hU4 : Nat.card U = 4)
    (hsq : ∀ x ∈ U, x * x = 1) {y : G} (hyN : ∀ x ∈ U, y * x * y⁻¹ ∈ U) (hy3 : y ^ 3 = 1)
    {a : G} (haU : a ∈ U) (hay : y * a * y⁻¹ ≠ a) :
    ∀ u ∈ U, ∃ w ∈ U, u = y * w * y⁻¹ * w⁻¹ := by
  classical
  obtain ⟨a', ha'⟩ : ∃ a' : G, a' = y * a * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨a'', ha''⟩ : ∃ a'' : G, a'' = y * a' * y⁻¹ := ⟨_, rfl⟩
  have ha'U : a' ∈ U := ha' ▸ hyN a haU
  have ha''U : a'' ∈ U := ha'' ▸ hyN a' ha'U
  have hay' : a' ≠ a := by rw [ha']; exact hay
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  have hcomm : ∀ x ∈ U, ∀ z ∈ U, x * z = z * x := fun x hx z hz => by
    have h1 := hsq (x * z) (U.mul_mem hx hz)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hsq z hz)
    calc x * z = (x * z)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = z * x := by rw [mul_inv_rev, hx', hz']
  have ha1 : a ≠ 1 := fun h => hay' (by rw [ha', h]; group)
  have ha'1 : a' ≠ 1 := fun h => ha1 (by
    have h1 : y * a * y⁻¹ = 1 := ha' ▸ h
    simpa [mul_inv_eq_one] using h1)
  have ha''1 : a'' ≠ 1 := fun h => ha'1 (by
    have h1 : y * a' * y⁻¹ = 1 := ha'' ▸ h
    simpa [mul_inv_eq_one] using h1)
  have ha''a' : a'' ≠ a' := fun h => hay' (by
    have h1 : y⁻¹ * a'' * y = y⁻¹ * a' * y := by rw [h]
    have e1 : y⁻¹ * a'' * y = a' := by rw [ha'']; group
    have e2 : y⁻¹ * a' * y = a := by rw [ha']; group
    rw [← e1, h1, e2])
  have hya'' : y * a'' * y⁻¹ = a := by
    calc y * a'' * y⁻¹ = (y * y * y) * a * (y * y * y)⁻¹ := by rw [ha'', ha']; group
      _ = a := by rw [hy3']; group
  have ha''a : a'' ≠ a := fun h => hay' (by
    have : y * a'' * y⁻¹ = y * a * y⁻¹ := by rw [h]
    rw [hya'', ← ha'] at this
    exact this.symm)
  have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  have hall : ∀ u ∈ U, u = 1 ∨ u = a ∨ u = a' ∨ u = a'' := by
    intro u hu
    by_contra hcon
    push Not at hcon
    obtain ⟨hu1, hua, hua', hua''⟩ := hcon
    have hsub : (({1, a, a', a'', u} : Finset G) : Set G) ⊆ (U : Set G) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [U.one_mem, haU, ha'U, ha''U, hu]
    have hcard5 : ({1, a, a', a'', u} : Finset G).card = 5 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ha1.symm, ha'1.symm, ha''1.symm, hu1.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hay'.symm, ha''a.symm, hua.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ha''a'.symm, hua'.symm⟩),
        Finset.card_pair hua''.symm]
    have : Finite U := Nat.finite_of_card_ne_zero (by omega)
    have h1 := Set.ncard_le_ncard hsub (U : Set G).toFinite
    rw [Set.ncard_coe_finset, hcard5, ← Nat.card_coe_set_eq] at h1
    have h2 : Nat.card (U : Set G) = 4 := hU4
    omega
  have haa' : a * a' = a'' := by
    rcases hall _ (U.mul_mem haU ha'U) with h | h | h | h
    · exact absurd (by rw [eq_inv_of_mul_eq_one_right h, hinv a haU]) hay'
    · exact absurd (mul_left_cancel (h.trans (mul_one a).symm)) ha'1
    · exact absurd (mul_right_cancel (h.trans (one_mul a').symm)) ha1
    · exact h
  intro u hu
  rcases hall u hu with hu' | hu' | hu' | hu'
  · exact ⟨1, U.one_mem, by rw [hu']; group⟩
  · refine ⟨a', ha'U, ?_⟩
    rw [hu', ← ha'', hinv a' ha'U, ← haa', mul_assoc, hsq a' ha'U, mul_one]
  · refine ⟨a'', ha''U, ?_⟩
    rw [hu', hya'', hinv a'' ha''U, ← haa', ← mul_assoc, hsq a haU, one_mul]
  · refine ⟨a, haU, ?_⟩
    rw [hu', ← ha', hinv a haU, ← haa']
    exact hcomm a haU a' ha'U

end CFSG.Quasithin.SBd19F
