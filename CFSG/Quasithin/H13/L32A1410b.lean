module

public import Certificates.Certificate7192
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.H13.L32NG5Model

public section

namespace CFSG.Quasithin.H13.G5ACert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert CFSG.Quasithin

theorem g5aCheck_eq : g5aCheck = true :=
  Certificates.certificate7192

theorem g5aCheck_parts :
    basicAB = true ∧ pAB = true ∧ ovAB = true ∧ oAB = true ∧ kAB = true := by
  have h := g5aCheck_eq
  simp only [g5aCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mem_tf (b : Bool) : b ∈ [true, false] := by cases b <;> simp

theorem gSAG_cols : gSAG = [colsOf (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5aS0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5aS1 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem gAAG_cols : gAAG = [colsOf (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5aA0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem gGA_unit (b : Bool) : ∀ c ∈ gGA b, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  intro c hc
  cases b
  · rw [show gGA false = gAAG from rfl, gAAG_cols] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨g5s0, (dec8_colsOf _).symm⟩
    · exact ⟨g5s1, (dec8_colsOf _).symm⟩
    · exact ⟨g5aA0, (dec8_colsOf _).symm⟩
    · exact ⟨g5aA1, (dec8_colsOf _).symm⟩
  · rw [show gGA true = gSAG from rfl, gSAG_cols] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨g5s0, (dec8_colsOf _).symm⟩
    · exact ⟨g5s1, (dec8_colsOf _).symm⟩
    · exact ⟨g5aS0, (dec8_colsOf _).symm⟩
    · exact ⟨g5aS1, (dec8_colsOf _).symm⟩

theorem gA5_eq (b : Bool) : g5 b false = genSub (gGA b) := by
  cases b
  · show Subgroup.closure _ = genSub gAAG
    unfold genSub
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, gAAG_cols,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl | rfl | rfl) <;> simp
    · rintro (h | h | h | h)
      · exact Or.inl (eq_of_colsOf_eq h)
      · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
      · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
      · exact Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h)))
  · show Subgroup.closure _ = genSub gSAG
    unfold genSub
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, gSAG_cols,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl | rfl | rfl) <;> simp
    · rintro (h | h | h | h)
      · exact Or.inl (eq_of_colsOf_eq h)
      · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
      · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
      · exact Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h)))

theorem gEA_eq (b : Bool) : gEA b = elemsOf (gGA b) := by cases b <;> rfl

theorem basicA_spec (b : Bool) :
    subB (gGA b) (elemsOf (gGA b)) = true ∧ (gEA b).length = nGA b := by
  have h := g5aCheck_parts.1
  simp only [basicAB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h b (mem_tf b)
  exact ⟨gEA_eq b ▸ h1, h2⟩

theorem mem_gA5_iff (b : Bool) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ g5 b false ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gEA b := by
  rw [gA5_eq, gEA_eq]
  exact mem_genSub_iff_of (basicA_spec b).1 (gGA_unit b) u

theorem card_gA5 (b : Bool) : Nat.card (g5 b false) = nGA b := by
  rw [gA5_eq, card_genSub_of (basicA_spec b).1 (gGA_unit b), ← gEA_eq]
  exact (basicA_spec b).2

theorem exists_mem_gA5 (b : Bool) {c : List ℕ} (hc : c ∈ gEA b) :
    ∃ u ∈ g5 b false, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  rw [gEA_eq] at hc
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  rw [gA5_eq]
  exact exists_evalW (gGA b) (subB_spec (basicA_spec b).1).2.2.2.2 (gGA_unit b) w

theorem genSub_le_gA5 (b : Bool) {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ gEA b) : genSub gens ≤ g5 b false :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_gA5_iff b u).mpr (hgens _ hu)

theorem unit_of_gEA (b : Bool) {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ gEA b) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_gA5 b (hgens g hg); ⟨u, hu⟩

theorem valid8_of_gEA (b : Bool) {c : List ℕ} (hc : c ∈ gEA b) :
    Valid8 c :=
  (subB_spec (basicA_spec b).1).1 _ (gEA_eq b ▸ hc)

@[expose] def PA5 (b : Bool) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (pGA b)

theorem pA_spec (b : Bool) :
    subB (pGA b) (pEA b) = true ∧ (pEA b).length = nPA b ∧ (∀ g ∈ pGA b, g ∈ gEA b) ∧
      ∀ v < 256, (∀ p ∈ pGA b, mv8 p v = v) → v = 0 ∨ v = vA := by
  have h := g5aCheck_parts.2.1
  simp only [pAB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h b (mem_tf b)
  refine ⟨h1, h2, h3, fun v hv hfix => ?_⟩
  rcases h4 v (List.mem_range.mpr hv) with (h | h) | h
  · exfalso
    have : ((pGA b).all fun p => mv8 p v == v) = true := by
      simp only [List.all_eq_true, beq_iff_eq]; exact hfix
    rw [this] at h
    exact Bool.noConfusion h
  · exact Or.inl h
  · exact Or.inr h

theorem PA5_le (b : Bool) : PA5 b ≤ g5 b false :=
  genSub_le_gA5 b (pA_spec b).2.2.1

theorem mem_PA5_iff (b : Bool) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ PA5 b ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ pEA b :=
  mem_genSub_iff_of (pA_spec b).1 (unit_of_gEA b (pA_spec b).2.2.1) u

theorem card_PA5 (b : Bool) : Nat.card (PA5 b) = nPA b := by
  rw [PA5, card_genSub_of (pA_spec b).1 (unit_of_gEA b (pA_spec b).2.2.1)]
  exact (pA_spec b).2.1

theorem eq_of_fixed_PA5 (b : Bool) (v : Fin 8 → ZMod 2)
    (hv : ∀ g ∈ PA5 b, (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = vec8 vA := by
  rcases (pA_spec b).2.2.2 (code8 v) (code8_lt v)
      (fixed_code (subB_spec (pA_spec b).1).2.2.2.2 (unit_of_gEA b (pA_spec b).2.2.1) hv)
    with h | h
  · exact Or.inl (by rw [← vec8_code8 v, h, vec8_zero])
  · exact Or.inr (by rw [← vec8_code8 v, h])

end CFSG.Quasithin.H13.G5ACert

end
