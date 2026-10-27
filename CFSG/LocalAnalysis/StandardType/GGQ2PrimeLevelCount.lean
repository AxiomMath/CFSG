module

public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GGQ2Prime

private def gq2Shift (v : Fin 6 → ZMod 3) (c : ZMod 3) : Finset (Equiv.Perm (Fin 6)) :=
  Finset.univ.filter fun π => ∀ i, v (π i) = v i + c

private theorem gq2_mem_shift {v : Fin 6 → ZMod 3} {c : ZMod 3} {π : Equiv.Perm (Fin 6)} :
    π ∈ gq2Shift v c ↔ ∀ i, v (π i) = v i + c := by
  simp [gq2Shift]

private theorem gq2_prod_zmod3 (g : ZMod 3 → ℕ) : ∏ a, g a = g 0 * g 1 * g 2 :=
  Fin.prod_univ_three g

private theorem gq2_sum_zmod3 (g : ZMod 3 → ℕ) : ∑ a, g a = g 0 + g 1 + g 2 :=
  Fin.sum_univ_three g

private theorem gq2_fibre_sum (v : Fin 6 → ZMod 3) :
    Fintype.card {i // v i = 0} + Fintype.card {i // v i = 1} +
      Fintype.card {i // v i = 2} = 6 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := v) (s := Finset.univ) (t := Finset.univ)
    (by intro x _; exact Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin, gq2_sum_zmod3] at h
  simp only [Fintype.card_subtype]
  omega

private theorem gq2_fibre_le {v : Fin 6 → ZMod 3} {π : Equiv.Perm (Fin 6)} {c a b : ZMod 3}
    (hπ : ∀ i, v (π i) = v i + c) (hb : b = a + c) :
    Fintype.card {i // v i = a} ≤ Fintype.card {i // v i = b} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  refine Finset.card_le_card_of_injOn (fun i => π i) ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show v (π i) = b
    rw [hπ i, hi.2, hb]
  · intro i _ j _ hij
    exact π.injective hij

private theorem gq2_fibres_eq {v : Fin 6 → ZMod 3} {π : Equiv.Perm (Fin 6)} {c : ZMod 3}
    (hc : c ≠ 0) (hπ : ∀ i, v (π i) = v i + c) :
    Fintype.card {i // v i = 0} = Fintype.card {i // v i = 1} ∧
      Fintype.card {i // v i = 1} = Fintype.card {i // v i = 2} := by
  have key : ∀ d : ZMod 3, d ≠ 0 → d = 1 ∨ d = 2 := by decide
  rcases key c hc with rfl | rfl
  · have h1 := gq2_fibre_le hπ (a := 0) (b := 1) (by decide)
    have h2 := gq2_fibre_le hπ (a := 1) (b := 2) (by decide)
    have h3 := gq2_fibre_le hπ (a := 2) (b := 0) (by decide)
    omega
  · have h1 := gq2_fibre_le hπ (a := 0) (b := 2) (by decide)
    have h2 := gq2_fibre_le hπ (a := 2) (b := 1) (by decide)
    have h3 := gq2_fibre_le hπ (a := 1) (b := 0) (by decide)
    omega

private theorem gq2_card_shift_zero (v : Fin 6 → ZMod 3) :
    (gq2Shift v 0).card = ∏ a, (Fintype.card {i // v i = a}).factorial := by
  rw [← DomMulAct.stabilizer_card v, Fintype.card_subtype]
  congr 1
  ext π
  simp [gq2Shift, funext_iff]

private theorem gq2_card_shift_le (v : Fin 6 → ZMod 3) (c : ZMod 3) :
    (gq2Shift v c).card ≤ (gq2Shift v 0).card := by
  by_cases h : ∃ π, π ∈ gq2Shift v c
  · obtain ⟨π, hπ⟩ := h
    have hπ' := gq2_mem_shift.mp hπ
    refine Finset.card_le_card_of_injOn (fun τ => τ * π⁻¹) ?_ ?_
    · intro τ hτ
      rw [Finset.mem_coe, gq2_mem_shift] at hτ
      rw [Finset.mem_coe, gq2_mem_shift]
      intro i
      simp only [Equiv.Perm.mul_apply, add_zero]
      have h1 := hτ (π⁻¹ i)
      have h2 := hπ' (π⁻¹ i)
      have hinv : π (π⁻¹ i) = i := by simp
      rw [hinv] at h2
      rw [h1, h2]
    · intro τ₁ _ τ₂ _ hτ
      exact mul_right_cancel hτ
  · have hempty : gq2Shift v c = ∅ := by
      ext π
      refine ⟨fun hπ => absurd (⟨π, hπ⟩ : ∃ x, x ∈ gq2Shift v c) h,
        fun hπ => absurd hπ (by simp)⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

private theorem gq2_fibre_shape {m₀ m₁ m₂ : ℕ} (hs : m₀ + m₁ + m₂ = 6)
    (hp : 120 ≤ m₀.factorial * m₁.factorial * m₂.factorial) :
    m₀ = 6 ∨ m₁ = 6 ∨ m₂ = 6 ∨ m₀ = 5 ∨ m₁ = 5 ∨ m₂ = 5 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hne
  have b0 : m₀ ≤ 4 := by omega
  have b1 : m₁ ≤ 4 := by omega
  have b2 : m₂ ≤ 4 := by omega
  interval_cases m₀ <;> interval_cases m₁ <;> interval_cases m₂ <;>
    first | omega | norm_num [Nat.factorial] at hp

private theorem gq2_const_of_six {v : Fin 6 → ZMod 3} {a : ZMod 3}
    (h : Fintype.card {i // v i = a} = 6) : ∀ i, v i = a := by
  intro i
  by_contra hne
  rw [Fintype.card_subtype] at h
  have hsub : Finset.univ.filter (fun j => v j = a) ⊆ Finset.univ.erase i := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    exact ⟨fun hji => hne (hji ▸ hj.2), Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hle
  omega

private theorem gq2_single_of_five {v : Fin 6 → ZMod 3} {a : ZMod 3}
    (h : Fintype.card {i // v i = a} = 5) :
    ∃ (i₀ : Fin 6) (c s : ZMod 3), s ≠ 0 ∧ ∀ i, v i = if i = i₀ then c + s else c := by
  rw [Fintype.card_subtype] at h
  have hcomp : (Finset.univ.filter fun j => v j = a).card +
      (Finset.univ.filter fun j => ¬ v j = a).card = 6 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 6)))
      (fun j => v j = a)
    simpa using this
  have hone : (Finset.univ.filter fun j => ¬ v j = a).card = 1 := by omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hone
  have hmem : ∀ i, ¬ v i = a ↔ i = i₀ := by
    intro i
    have := Finset.ext_iff.mp hi₀ i
    simpa using this
  refine ⟨i₀, a, v i₀ - a, sub_ne_zero.mpr ((hmem i₀).mpr rfl), ?_⟩
  intro i
  by_cases hi : i = i₀
  · rw [if_pos hi, hi]
    ring
  · rw [if_neg hi]
    by_contra hne
    exact hi ((hmem i).mp hne)

theorem eq_const_or_single_of_le_card {v : Fin 6 → ZMod 3} {S : Finset (Equiv.Perm (Fin 6))}
    (hS : 120 ≤ S.card) (hv : ∀ π ∈ S, ∃ c : ZMod 3, ∀ i, v (π i) = v i + c) :
    (∃ c, ∀ i, v i = c) ∨
      ∃ (i₀ : Fin 6) (c s : ZMod 3), s ≠ 0 ∧ ∀ i, v i = if i = i₀ then c + s else c := by
  have hc3 : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  by_cases hcyc : ∃ π ∈ S, ∃ c : ZMod 3, c ≠ 0 ∧ ∀ i, v (π i) = v i + c
  · exfalso
    obtain ⟨π, _, c, hc0, hπ⟩ := hcyc
    obtain ⟨e1, e2⟩ := gq2_fibres_eq hc0 hπ
    have hs := gq2_fibre_sum v
    have hf0 : Fintype.card {i // v i = 0} = 2 := by omega
    have hf1 : Fintype.card {i // v i = 1} = 2 := by omega
    have hf2 : Fintype.card {i // v i = 2} = 2 := by omega
    have h8 : (gq2Shift v 0).card = 8 := by
      rw [gq2_card_shift_zero, gq2_prod_zmod3, hf0, hf1, hf2]
      rfl
    have hsub : S ⊆ gq2Shift v 0 ∪ gq2Shift v 1 ∪ gq2Shift v 2 := by
      intro π' hπ'
      obtain ⟨c', hc'⟩ := hv π' hπ'
      rcases hc3 c' with rfl | rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (gq2_mem_shift.mpr hc'))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (gq2_mem_shift.mpr hc'))
      · exact Finset.mem_union_right _ (gq2_mem_shift.mpr hc')
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (gq2Shift v 0 ∪ gq2Shift v 1) (gq2Shift v 2)
    have h3 := Finset.card_union_le (gq2Shift v 0) (gq2Shift v 1)
    have h4 := gq2_card_shift_le v 1
    have h5 := gq2_card_shift_le v 2
    omega
  · have hS0 : S ⊆ gq2Shift v 0 := by
      intro π hπ
      obtain ⟨c, hc⟩ := hv π hπ
      rw [gq2_mem_shift]
      by_cases hc0 : c = 0
      · subst hc0
        exact hc
      · exact absurd ⟨π, hπ, c, hc0, hc⟩ hcyc
    have hle : S.card ≤ (gq2Shift v 0).card := Finset.card_le_card hS0
    rw [gq2_card_shift_zero, gq2_prod_zmod3] at hle
    have hp := le_trans hS hle
    rcases gq2_fibre_shape (gq2_fibre_sum v) hp with h | h | h | h | h | h
    · exact Or.inl ⟨0, gq2_const_of_six h⟩
    · exact Or.inl ⟨1, gq2_const_of_six h⟩
    · exact Or.inl ⟨2, gq2_const_of_six h⟩
    · exact Or.inr (gq2_single_of_five h)
    · exact Or.inr (gq2_single_of_five h)
    · exact Or.inr (gq2_single_of_five h)

end CFSG.GGQ2Prime
