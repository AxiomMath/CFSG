module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

namespace OrthTorus

@[expose] def simpleLo {r : ℕ} (i : Fin r) : Fin r :=
  ⟨if i.val + 1 < r then i.val else r - 2, by have := i.isLt; split_ifs <;> omega⟩

@[expose] def simpleHi {r : ℕ} (i : Fin r) : Fin r :=
  ⟨if i.val + 1 < r then i.val + 1 else r - 1, by have := i.isLt; split_ifs <;> omega⟩

theorem simpleLo_of_lt {r : ℕ} {i : Fin r} (h : i.val + 1 < r) : (simpleLo i).val = i.val := by
  simp only [simpleLo, Fin.val_mk, if_pos h]

theorem simpleHi_of_lt {r : ℕ} {i : Fin r} (h : i.val + 1 < r) : (simpleHi i).val = i.val + 1 := by
  simp only [simpleHi, Fin.val_mk, if_pos h]

theorem simpleLo_of_last {r : ℕ} {i : Fin r} (h : i.val + 1 = r) : (simpleLo i).val = r - 2 := by
  simp only [simpleLo, Fin.val_mk, if_neg (by omega : ¬ i.val + 1 < r)]

theorem simpleHi_of_last {r : ℕ} {i : Fin r} (h : i.val + 1 = r) : (simpleHi i).val = r - 1 := by
  simp only [simpleHi, Fin.val_mk, if_neg (by omega : ¬ i.val + 1 < r)]

theorem simpleLo_ne_simpleHi {r : ℕ} (hr : 2 ≤ r) (i : Fin r) : simpleLo i ≠ simpleHi i := by
  intro h
  have hv := congrArg Fin.val h
  by_cases hi : i.val + 1 < r
  · rw [simpleLo_of_lt hi, simpleHi_of_lt hi] at hv
    omega
  · have hlast : i.val + 1 = r := by have := i.isLt; omega
    rw [simpleLo_of_last hlast, simpleHi_of_last hlast] at hv
    omega

private lemma q2cO5c_cartanD_ne_zero_iff {r : ℕ} (hr : 3 ≤ r) {i j : Fin r} (hij : i ≠ j) :
    CartanMatrix.D r i j ≠ 0 ↔
      (j.val = i.val + 1 ∧ j.val + 1 < r) ∨ (i.val = j.val + 1 ∧ i.val + 1 < r) ∨
        (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r) := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  rw [if_neg hij, if_neg (by omega : ¬ r ≤ 2)]
  by_cases h1 : i.val + 1 = j.val ∧ j.val + 2 < r
  · rw [if_pos h1]
    constructor
    · intro _; left; omega
    · intro _; norm_num
  · rw [if_neg h1]
    by_cases h2 : j.val + 1 = i.val ∧ i.val + 2 < r
    · rw [if_pos h2]
      constructor
      · intro _; right; left; omega
      · intro _; norm_num
    · rw [if_neg h2]
      by_cases h3 : i.val + 3 = r ∧ (j.val + 2 = r ∨ j.val + 1 = r)
      · rw [if_pos h3]
        constructor
        · intro _
          rcases h3 with ⟨h3a, h3b | h3b⟩
          · left; omega
          · exact Or.inr (Or.inr (Or.inl ⟨h3a, h3b⟩))
        · intro _; norm_num
      · rw [if_neg h3]
        by_cases h4 : j.val + 3 = r ∧ (i.val + 2 = r ∨ i.val + 1 = r)
        · rw [if_pos h4]
          constructor
          · intro _
            rcases h4 with ⟨h4a, h4b | h4b⟩
            · right; left; omega
            · exact Or.inr (Or.inr (Or.inr ⟨h4a, h4b⟩))
          · intro _; norm_num
        · rw [if_neg h4]
          constructor
          · intro h0; exact absurd rfl h0
          · rintro (hR | hR | hR | hR)
            · have hjr : j.val + 2 < r := by
                by_contra hc
                exact h3 ⟨by omega, Or.inl (by omega)⟩
              exact fun _ => h1 ⟨by omega, hjr⟩
            · have hir : i.val + 2 < r := by
                by_contra hc
                exact h4 ⟨by omega, Or.inl (by omega)⟩
              exact fun _ => h2 ⟨by omega, hir⟩
            · exact fun _ => h3 ⟨hR.1, Or.inr hR.2⟩
            · exact fun _ => h4 ⟨hR.1, Or.inr hR.2⟩

theorem ggCoxeterMatrixD_eq_three_iff {r : ℕ} (hr : 3 ≤ r) (i j : Fin r) :
    ggCoxeterMatrixD r i j = 3 ↔
      (j.val = i.val + 1 ∧ j.val + 1 < r) ∨ (i.val = j.val + 1 ∧ i.val + 1 < r) ∨
        (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r) := by
  rw [ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    have hv : i.val = j.val := by rw [hij]
    constructor
    · intro h; exact absurd h (by norm_num)
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rw [if_neg hij]
    by_cases hD : CartanMatrix.D r i j = 0
    · rw [if_pos hD]
      constructor
      · intro h; exact absurd h (by norm_num)
      · intro hR; exact absurd hD ((q2cO5c_cartanD_ne_zero_iff hr hij).mpr hR)
    · rw [if_neg hD]
      exact ⟨fun _ => (q2cO5c_cartanD_ne_zero_iff hr hij).mp hD, fun _ => rfl⟩

theorem ggCoxeterMatrixD_eq_two_cases {r : ℕ} (hr : 4 ≤ r) {i j : Fin r} (hij : i ≠ j)
    (h : ggCoxeterMatrixD r i j = 2) :
    Disjoint ({simpleLo i, simpleHi i} : Finset (Fin r)) {simpleLo j, simpleHi j} ∨
      (i.val + 2 = r ∧ j.val + 1 = r) ∨ (i.val + 1 = r ∧ j.val + 2 = r) := by
  have hr3 : 3 ≤ r := by omega
  have hR3 : ¬ ((j.val = i.val + 1 ∧ j.val + 1 < r) ∨
      (i.val = j.val + 1 ∧ i.val + 1 < r) ∨
      (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r)) := by
    intro hR
    have h3 := (ggCoxeterMatrixD_eq_three_iff hr3 i j).mpr hR
    omega
  have hA : ¬ (j.val = i.val + 1 ∧ j.val + 1 < r) := fun hA => hR3 (Or.inl hA)
  have hB : ¬ (i.val = j.val + 1 ∧ i.val + 1 < r) := fun hB => hR3 (Or.inr (Or.inl hB))
  have hC : ¬ (i.val + 3 = r ∧ j.val + 1 = r) :=
    fun hC => hR3 (Or.inr (Or.inr (Or.inl hC)))
  have hD : ¬ (j.val + 3 = r ∧ i.val + 1 = r) :=
    fun hD => hR3 (Or.inr (Or.inr (Or.inr hD)))
  by_cases hilt : i.val + 1 < r
  · by_cases hjlt : j.val + 1 < r
    · left
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      have hxi : x.val = i.val ∨ x.val = i.val + 1 := by
        rcases hx with hx | hx
        · left; rw [hx, simpleLo_of_lt hilt]
        · right; rw [hx, simpleHi_of_lt hilt]
      have hxj : x.val = j.val ∨ x.val = j.val + 1 := by
        rcases hy with hy | hy
        · left; rw [hy, simpleLo_of_lt hjlt]
        · right; rw [hy, simpleHi_of_lt hjlt]
      rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
      · exact hij (Fin.ext (by omega))
      · exact hB ⟨by omega, hilt⟩
      · exact hA ⟨by omega, hjlt⟩
      · exact hij (Fin.ext (by omega))
    · have hjlast : j.val + 1 = r := by have := j.isLt; omega
      by_cases hij2 : i.val + 2 = r
      · exact Or.inr (Or.inl ⟨hij2, hjlast⟩)
      · refine Or.inl ?_
        rw [Finset.disjoint_left]
        intro x hx hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        have hxi : x.val = i.val ∨ x.val = i.val + 1 := by
          rcases hx with hx | hx
          · left; rw [hx, simpleLo_of_lt hilt]
          · right; rw [hx, simpleHi_of_lt hilt]
        have hxj : x.val = r - 2 ∨ x.val = r - 1 := by
          rcases hy with hy | hy
          · left; rw [hy, simpleLo_of_last hjlast]
          · right; rw [hy, simpleHi_of_last hjlast]
        have hi3 : i.val + 3 ≠ r := fun hc => hC ⟨hc, hjlast⟩
        omega
  · have hilast : i.val + 1 = r := by have := i.isLt; omega
    by_cases hjlt : j.val + 1 < r
    · by_cases hji2 : j.val + 2 = r
      · exact Or.inr (Or.inr ⟨hilast, hji2⟩)
      · refine Or.inl ?_
        rw [Finset.disjoint_left]
        intro x hx hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        have hxi : x.val = r - 2 ∨ x.val = r - 1 := by
          rcases hx with hx | hx
          · left; rw [hx, simpleLo_of_last hilast]
          · right; rw [hx, simpleHi_of_last hilast]
        have hxj : x.val = j.val ∨ x.val = j.val + 1 := by
          rcases hy with hy | hy
          · left; rw [hy, simpleLo_of_lt hjlt]
          · right; rw [hy, simpleHi_of_lt hjlt]
        have hj3 : j.val + 3 ≠ r := fun hc => hD ⟨hc, hilast⟩
        omega
    · exfalso
      have hjlast : j.val + 1 = r := by have := j.isLt; omega
      exact hij (Fin.ext (by omega))

end OrthTorus

end CFSG.StandardType

end
