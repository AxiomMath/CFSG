module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutBridge

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut

@[expose] def s6InvTbl : List (List ℕ × List ℕ × List ℕ) := [
  ([0, 4, 2, 3, 1, 5, 8, 9, 6, 7], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7], [0, 6, 5, 2, 8, 3, 7, 1, 9, 4]),
  ([9, 2, 1, 6, 4, 5, 3, 7, 8, 0], [4, 2, 7, 6, 9, 3, 5, 1, 8, 0], [2, 3, 6, 9, 7, 4, 0, 5, 8, 1]),
  ([4, 3, 2, 1, 0, 5, 6, 7, 9, 8], [2, 3, 4, 5, 0, 1, 9, 7, 6, 8], [3, 9, 5, 8, 1, 6, 2, 7, 0, 4]),
  ([7, 1, 4, 8, 2, 5, 6, 0, 3, 9], [1, 7, 9, 8, 2, 3, 6, 0, 5, 4], [2, 9, 8, 7, 3, 1, 6, 4, 0, 5]),
  ([2, 1, 0, 5, 4, 3, 8, 7, 6, 9], [1, 2, 0, 4, 5, 3, 7, 8, 6, 9], [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]),
  ([0, 3, 6, 1, 4, 7, 2, 5, 8, 9], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7], [0, 6, 5, 2, 8, 3, 7, 1, 9, 4]),
  ([0, 6, 3, 2, 8, 5, 1, 7, 4, 9], [0, 6, 5, 2, 8, 3, 7, 1, 9, 4], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7]),
  ([0, 7, 2, 5, 9, 3, 6, 1, 8, 4], [0, 6, 5, 2, 8, 3, 7, 1, 9, 4], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7]),
  ([9, 1, 2, 3, 8, 7, 6, 5, 4, 0], [1, 9, 2, 8, 3, 7, 5, 6, 4, 0], [4, 3, 2, 6, 7, 9, 1, 0, 5, 8]),
  ([0, 1, 5, 3, 4, 2, 7, 6, 9, 8], [0, 6, 5, 2, 8, 3, 7, 1, 9, 4], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7]),
  ([4, 1, 7, 3, 0, 6, 5, 2, 8, 9], [1, 4, 9, 3, 0, 8, 5, 2, 6, 7], [2, 9, 5, 3, 7, 0, 4, 6, 1, 8]),
  ([2, 9, 0, 3, 7, 5, 6, 4, 8, 1], [2, 3, 6, 9, 7, 4, 0, 5, 8, 1], [4, 2, 7, 6, 9, 3, 5, 1, 8, 0]),
  ([6, 7, 8, 3, 4, 5, 0, 1, 2, 9], [3, 4, 5, 6, 7, 8, 0, 1, 2, 9], [1, 2, 0, 4, 5, 3, 7, 8, 6, 9]),
  ([3, 4, 5, 0, 1, 2, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8, 0, 1, 2, 9], [1, 2, 0, 4, 5, 3, 7, 8, 6, 9]),
  ([0, 1, 2, 6, 7, 8, 3, 4, 5, 9], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1]),
  ([0, 5, 4, 3, 2, 1, 9, 7, 8, 6], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1]),
  ([1, 0, 9, 3, 4, 8, 6, 7, 5, 2], [1, 3, 6, 0, 4, 7, 9, 8, 5, 2], [8, 5, 1, 7, 4, 2, 3, 6, 9, 0]),
  ([0, 1, 8, 4, 3, 9, 6, 7, 2, 5], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7], [0, 6, 5, 2, 8, 3, 7, 1, 9, 4]),
  ([7, 6, 2, 3, 4, 9, 1, 0, 8, 5], [2, 6, 7, 9, 4, 3, 8, 0, 1, 5], [5, 7, 3, 8, 4, 6, 0, 9, 2, 1]),
  ([5, 8, 2, 3, 6, 0, 4, 7, 1, 9], [2, 9, 5, 3, 7, 0, 4, 6, 1, 8], [1, 4, 9, 3, 0, 8, 5, 2, 6, 7]),
  ([6, 1, 2, 9, 5, 4, 0, 7, 8, 3], [1, 6, 3, 9, 5, 8, 0, 7, 4, 2], [5, 8, 1, 6, 3, 9, 4, 7, 2, 0]),
  ([0, 9, 2, 8, 4, 6, 5, 7, 3, 1], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6]),
  ([0, 1, 9, 7, 6, 5, 4, 3, 8, 2], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6]),
  ([3, 1, 2, 0, 4, 5, 9, 8, 7, 6], [1, 3, 6, 0, 4, 7, 9, 8, 5, 2], [8, 5, 1, 7, 4, 2, 3, 6, 9, 0]),
  ([8, 1, 6, 3, 9, 5, 2, 7, 0, 4], [1, 8, 6, 9, 3, 5, 7, 2, 0, 4], [4, 3, 8, 7, 6, 5, 0, 1, 9, 2]),
  ([5, 1, 3, 2, 4, 0, 6, 9, 8, 7], [1, 5, 3, 4, 2, 0, 9, 6, 8, 7], [3, 4, 9, 7, 6, 2, 1, 0, 8, 5]),
  ([0, 8, 7, 9, 4, 5, 6, 2, 1, 3], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1]),
  ([0, 2, 1, 3, 5, 4, 6, 8, 7, 9], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6]),
  ([8, 5, 2, 7, 4, 1, 6, 3, 0, 9], [2, 9, 8, 7, 3, 1, 6, 4, 0, 5], [1, 7, 9, 8, 2, 3, 6, 0, 5, 4]),
  ([1, 0, 2, 4, 3, 5, 7, 6, 8, 9], [1, 2, 0, 4, 5, 3, 7, 8, 6, 9], [3, 4, 5, 6, 7, 8, 0, 1, 2, 9])
]

@[expose] def nineInj (e1 e2 : List ℕ) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j => (List.range 3).all fun i' =>
    (List.range 3).all fun j' =>
      Core.cmul (Core.cpow e1 i) (Core.cpow e2 j) !=
          Core.cmul (Core.cpow e1 i') (Core.cpow e2 j') || (i == i' && j == j')

@[expose] def s6EntryOK (t : List ℕ × List ℕ × List ℕ) : Bool :=
  Core.pslLit.contains t.2.1 && Core.pslLit.contains t.2.2 &&
    Core.cpow t.2.1 3 == Core.cid && Core.cpow t.2.2 3 == Core.cid &&
    Core.cmul t.2.1 t.2.2 == Core.cmul t.2.2 t.2.1 && nineInj t.2.1 t.2.2 &&
    Core.cmul (Core.cmul t.1 t.2.1) (invC t.1) == invC t.2.1 &&
    Core.cmul (Core.cmul t.1 t.2.2) (invC t.1) == t.2.2

theorem s6Inv_check : Core.autL.all (fun c => Core.cmul c c != Core.cid || c == Core.cid ||
    Core.pslLit.contains c || !Core.inS6 c ||
      s6InvTbl.any (fun t => t.1 == c && s6EntryOK t)) = true := by
  decide +kernel

theorem exists_s6_pair {α : P10} (hα : α ∈ A6Models.autA6) (h2 : α * α = 1) (hne : α ≠ 1)
    (hpsl : α ∉ A6Models.psl29) (hs6 : α ∈ s6) :
    ∃ e₁ ∈ A6Models.psl29, ∃ e₂ ∈ A6Models.psl29, e₁ ^ 3 = 1 ∧ e₂ ^ 3 = 1 ∧
      e₁ * e₂ = e₂ * e₁ ∧
      (∀ i j i' j' : Fin 3, e₁ ^ (i : ℕ) * e₂ ^ (j : ℕ) = e₁ ^ (i' : ℕ) * e₂ ^ (j' : ℕ) →
        i = i' ∧ j = j') ∧
      α * e₁ * α⁻¹ = e₁⁻¹ ∧ α * e₂ * α⁻¹ = e₂ := by
  have h := s6Inv_check
  rw [List.all_eq_true] at h
  have h1 := h (code α) (code_mem_autL hα)
  have e1 : (Core.cmul (code α) (code α) != Core.cid) = false := by
    rw [← code_mul, h2, code_one]
    simp
  have e2 : (code α == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro hc
    exact hne (code_injective hc)
  have e3 : Core.pslLit.contains (code α) = false := by
    rw [← Bool.not_eq_true, List.contains_iff_mem, ← mem_psl29_iff]
    exact hpsl
  have e4 : (!Core.inS6 (code α)) = false := by
    rw [(mem_s6_iff α).mp hs6]
    rfl
  rw [e1, e2, e3, e4] at h1
  simp only [Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨b, c₁, c₂⟩, -, hb, hok⟩ := h1
  simp only at hb
  subst hb
  simp only [s6EntryOK, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hc₁, hc₂⟩, h31⟩, h32⟩, hcomm⟩, hnd⟩, hinv⟩, hfix⟩ := hok
  obtain ⟨x₁, hx₁, rfl⟩ := exists_psl29_of_code hc₁
  obtain ⟨x₂, hx₂, rfl⟩ := exists_psl29_of_code hc₂
  refine ⟨x₁, hx₁, x₂, hx₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply code_injective
    rw [code_pow, h31, code_one]
  · apply code_injective
    rw [code_pow, h32, code_one]
  · apply code_injective
    rw [code_mul, code_mul, hcomm]
  · intro i j i' j' hij
    have hc := congrArg code hij
    rw [code_mul, code_mul, code_pow, code_pow, code_pow, code_pow] at hc
    simp only [nineInj, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Bool.and_eq_true, beq_iff_eq] at hnd
    rcases hnd i i.2 j j.2 i' i'.2 j' j'.2 with h | ⟨h1, h2⟩
    · exact absurd hc h
    · exact ⟨Fin.ext h1, Fin.ext h2⟩
  · apply code_injective
    rw [code_mul, code_mul, code_inv, code_inv, hinv]
  · apply code_injective
    rw [code_mul, code_mul, code_inv, hfix]

end CFSG.Quasithin.H13.A5
