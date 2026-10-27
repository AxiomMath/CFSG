module

public import CFSG.Quasithin.H13.L32A1410b

public section

namespace CFSG.Quasithin.H13.G5ACert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert CFSG.Quasithin

@[expose] def MA5 (b : Bool) (i : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) :=
  genSub (pGA b ++ [(mRA b).getD i one8])

theorem ovA_spec (b : Bool) :
    (mRA b).length = 2 ∧ (∀ r ∈ mRA b, r ∈ gEA b) ∧
      (∀ i ∈ [0, 1], (mEA b i).length = 3 * nPA b ∧
        subB (pGA b ++ [(mRA b).getD i one8]) (mEA b i) = true) ∧
      ∀ y ∈ gEA b, y ∈ pEA b ∨
        (3 * nPA b + 1 ≤ (elemsOf (pGA b ++ [y]) (3 * nPA b + 1)).length ∧
          nodupB (elemsOf (pGA b ++ [y]) (3 * nPA b + 1)) = true) ∨
        ((elemsOf (pGA b ++ [y]) (3 * nPA b + 1)).length = 3 * nPA b ∧
          nodupB (elemsOf (pGA b ++ [y]) (3 * nPA b + 1)) = true ∧
          ∃ i ∈ [0, 1], ∀ c ∈ elemsOf (pGA b ++ [y]) (3 * nPA b + 1), c ∈ mEA b i) := by
  have h := g5aCheck_parts.2.2.1
  simp only [ovAB, List.all_eq_true] at h
  have h' := h b (mem_tf b)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_map] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  rcases h4 y hy with h | h | ⟨⟨h5, h6⟩, ⟨_, ⟨i, hi, rfl⟩, h7⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h5, h6, i, hi, fun c hc => ?_⟩)
    have := h7 c hc
    simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using this

theorem mRA_mem (b : Bool) {i : ℕ} (hi : i < 2) :
    (mRA b).getD i one8 ∈ gEA b := by
  rw [List.getD_eq_getElem _ _ (by rw [(ovA_spec b).1]; exact hi)]
  exact (ovA_spec b).2.1 _ (List.getElem_mem _)

theorem MA5_gens_mem (b : Bool) {i : ℕ} (hi : i < 2) :
    ∀ g ∈ pGA b ++ [(mRA b).getD i one8], g ∈ gEA b := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (pA_spec b).2.2.1 g hg
  · rw [List.mem_singleton.mp hg]; exact mRA_mem b hi

theorem mEA_spec (b : Bool) {i : ℕ} (hi : i < 2) :
    (mEA b i).length = 3 * nPA b ∧ subB (pGA b ++ [(mRA b).getD i one8]) (mEA b i) = true :=
  (ovA_spec b).2.2.1 i (by interval_cases i <;> simp)

theorem mem_MA5_iff (b : Bool) {i : ℕ} (hi : i < 2)
    (u : GL (Fin 8) (ZMod 2)) :
    u ∈ MA5 b i ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ mEA b i :=
  mem_genSub_iff_of (mEA_spec b hi).2 (unit_of_gEA b (MA5_gens_mem b hi)) u

end CFSG.Quasithin.H13.G5ACert

end
