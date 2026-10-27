module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocV

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

@[expose] def chkT1 : Bool := (List.range 45).all fun q => (List.range 27).all fun k =>
  !sameSet (imgSet (tpTab.getD q []) (lnTab.getD k [])) (lnTab.getD k []) ||
    (lnTab.getD k []).contains q

@[expose] def chkT2 : Bool := (List.range 45).all fun q => xL.getD q 0 != q ||
  (List.range 27).any fun k => (lnTab.getD k []).contains 0 && (lnTab.getD k []).contains q

theorem chkT1_true : chkT1 = true := by decide +kernel

theorem chkT2_true : chkT2 = true := by decide +kernel

@[expose] def fixSet (g : Y) : Set (Fin 45) := {p | (g : P45) p = p}

theorem fixSet_conj (k a : Y) : fixSet (k * a * k⁻¹) = (k : P45) '' fixSet a := by
  ext p
  simp only [fixSet, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨((k : Y) : P45)⁻¹ p, ?_, by simp⟩
    have h1 : (k : P45) ((a : P45) (((k : Y) : P45)⁻¹ p)) = p := by
      have := h
      simpa [Equiv.Perm.mul_apply] using this
    exact (k : P45).injective (by rw [h1]; simp)
  · rintro ⟨q, hq, rfl⟩
    simp [Equiv.Perm.mul_apply, hq]

theorem fixSet_tY : fixSet tY = L0S := by
  ext p
  exact fix_t_iff p

theorem exists_image_of_isConj_tY {a : Y} (h : IsConj tY a) :
    ∃ k : Y, fixSet a = (k : P45) '' L0S := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact ⟨c, by rw [← hc, fixSet_conj, fixSet_tY]⟩

theorem fixSet_eq_image_of_isConj_tY {a : Y} (h : IsConj tY a) :
    (fixSet a).ncard = 5 := by
  obtain ⟨k, hk⟩ := exists_image_of_isConj_tY h
  rw [hk, Set.ncard_image_of_injective _ (k : P45).injective, L0S_ncard]

theorem exists_line_eq_image (k : Y) :
    ∃ j < 27, (k : P45) '' L0S = lnS j := by
  have h := line_stable k.2 (k := 0) (by norm_num)
  have h0 : lnS 0 = L0S := by
    rw [lnS, lines_spec.2.1]
    rfl
  rw [h0] at h
  exact h

theorem mem_of_image_eq {q : Fin 45} {j : ℕ} (hj : j < 27)
    (h : (sY q : P45) '' lnS j = lnS j) : q ∈ lnS j := by
  have h1 := chkT1_true
  simp only [chkT1, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h1
  have h2 := h1 q.val q.2 j hj
  have h3 : (sY q : P45) '' lineSet (lnTab.getD j []) = lineSet (lnTab.getD j []) := h
  rw [image_lineSet (repL_sY q) (lnTab_lt hj)] at h3
  rcases h2 with h2 | h2
  · exact absurd (sameSet_of_lineSet_eq h3) (by rw [h2]; simp)
  · exact List.contains_iff_mem.1 h2

theorem mem_line_of_fix {q : Fin 45} {k : Y}
    (h : (sY q : P45) '' ((k : P45) '' L0S) = (k : P45) '' L0S) : q ∈ (k : P45) '' L0S := by
  obtain ⟨j, hj, hjk⟩ := exists_line_eq_image k
  rw [hjk] at h ⊢
  exact mem_of_image_eq hj h

theorem exists_line_of_fix_x {q : Fin 45} (hq : (x45 q) = q) :
    ∃ j < 27, (0 : Fin 45) ∈ lnS j ∧ q ∈ lnS j := by
  have h := chkT2_true
  simp only [chkT2, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  have hq' : xL.getD q 0 = q := by rw [repL_x.2 q, hq]
  rcases h q.val q.2 with h1 | ⟨j, hj, h0, hqj⟩
  · exact absurd hq' h1
  · exact ⟨j, hj, h0, hqj⟩

theorem exists_P1_line {j : ℕ} (hj : j < 27)
    (h0 : (0 : Fin 45) ∈ lnS j) : ∃ m ∈ P1, (m : P45) '' L0S = lnS j := by
  have hfilt := p_spec.2.2.1
  have hmem : j ∈ (List.range 27).filter (fun k => (lnTab.getD k []).contains 0) := by
    simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
    exact ⟨hj, h0⟩
  rw [hfilt] at hmem
  obtain ⟨kw, hkw, hkwe⟩ := List.mem_map.1 hmem
  obtain ⟨g, hg, hgS⟩ := P1_elem hkw
  rw [hkwe, smul_set_eq] at hgS
  exact ⟨g, hg, hgS⟩

end CFSG.Quasithin.H13.F431.U42
