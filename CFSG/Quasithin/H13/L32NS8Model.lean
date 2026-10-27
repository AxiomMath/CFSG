module

public import CFSG.Quasithin.H13.L32NS7Model
public import Certificates.Certificate7175

public section

namespace CFSG.Quasithin.H13.S8Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert

theorem s8Check_eq : s8Check = true :=
  Certificates.certificate7175

theorem s8Check_parts :
    s8BasicB = true ∧ stabIB = true ∧ orbB = true ∧ zB = true ∧ nB = true ∧ wB = true ∧
      fB = true := by
  have h := s8Check_eq
  simp only [s8Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem s8G_cols : s8G = [colsOf (s8g0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (s8g1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (s8g2 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (s8g3 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (s8g4 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem s8G_unit : ∀ g ∈ s8G, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  rw [s8G_cols]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact ⟨s8g0, (dec8_colsOf _).symm⟩
  · exact ⟨s8g1, (dec8_colsOf _).symm⟩
  · exact ⟨s8g2, (dec8_colsOf _).symm⟩
  · exact ⟨s8g3, (dec8_colsOf _).symm⟩
  · exact ⟨s8g4, (dec8_colsOf _).symm⟩

theorem s8_eq : s8 = genSub s8G := by
  unfold s8 genSub
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, s8G_cols,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
  · rintro (h | h | h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h))))

theorem s8Basic_spec :
    subB s8G s8E = true ∧ s8E.length = 40320 := by
  have h := s8Check_parts.1
  simp only [s8BasicB, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem mem_s8_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ s8 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ s8E := by
  rw [s8_eq]
  exact mem_genSub_iff_of s8Basic_spec.1 s8G_unit u

theorem card_s8 : Nat.card s8 = 40320 := by
  rw [s8_eq, card_genSub_of s8Basic_spec.1 s8G_unit]
  exact s8Basic_spec.2

theorem exists_mem_s8 {c : List ℕ} (hc : c ∈ s8E) :
    ∃ u ∈ s8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  rw [s8_eq]
  exact exists_evalW s8G (subB_spec s8Basic_spec.1).2.2.2.2 s8G_unit w

theorem genSub_le_s8 {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ s8E) : genSub gens ≤ s8 :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_s8_iff u).mpr (hgens _ hu)

theorem unit_of_s8E {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ s8E) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_s8 (hgens g hg); ⟨u, hu⟩

theorem colsOf_mem_s8E {u : GL (Fin 8) (ZMod 2)} (hu : u ∈ s8) :
    colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ s8E := (mem_s8_iff u).mp hu

theorem mem_subI_of_cols {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hM : ∀ c ∈ (colsOf M).take 4, c < 16) {u : Fin 8 → ZMod 2} (hu : u ∈ subI) :
    M.mulVec u ∈ subI := by
  have hcol : ∀ i j : Fin 8, 4 ≤ (i : ℕ) → (j : ℕ) < 4 → M i j = 0 := by
    intro i j hi hj
    have hmem : code8 (fun i => M i j) ∈ (colsOf M).take 4 := by
      fin_cases j <;> simp [colsOf, List.ofFn_succ] at hj ⊢
    have hlt := hM _ hmem
    have h1 : M i j = vec8 (code8 (fun i => M i j)) i := by rw [vec8_code8]
    rw [h1]
    simp only [vec8, b2z]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (i : ℕ) := Nat.pow_le_pow_right (by norm_num) hi))]
    rfl
  intro i hi
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  rw [hcol i 0 hi (by decide), hcol i 1 hi (by decide), hcol i 2 hi (by decide),
    hcol i 3 hi (by decide), hu 4 (by decide), hu 5 (by decide), hu 6 (by decide),
    hu 7 (by decide)]
  ring

theorem mem_subI_of_fix {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ s8)
    {v : ℕ} (hv : v ∈ iiList)
    (hfix : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 v) = vec8 v)
    {u : Fin 8 → ZMod 2} (hu : u ∈ subI) :
    (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec u ∈ subI := by
  have h := s8Check_parts.2.1
  simp only [stabIB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    decide_eq_true_eq] at h
  have hv256 : v < 256 := List.mem_range.mp (List.mem_filter.mp hv).1
  rcases h _ (colsOf_mem_s8E hy) v hv with h1 | h1
  · exfalso
    apply h1
    rw [mulVec_vec8] at hfix
    exact vec8_inj (mv8_lt (valid8_colsOf _) _) hv256 hfix
  · exact mem_subI_of_cols h1 hu

theorem exists_mem_s8_vR {v : ℕ} (hv : v < 256) (hv0 : v ≠ 0)
    (hII : inII v = false) (hq : q4N v = false) :
    ∃ y ∈ s8, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 v := by
  have h := s8Check_parts.2.2.1
  simp only [orbB, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  rcases h v (List.mem_range.mpr hv) with ((h1 | h1) | h1) | h1
  · exact absurd h1 hv0
  · rw [hII] at h1; exact absurd h1 (by decide)
  · rw [hq] at h1; exact absurd h1 (by decide)
  · obtain ⟨c, hc, hcv⟩ := List.mem_map.mp h1
    obtain ⟨y, hy, hyc⟩ := exists_mem_s8 hc
    refine ⟨y, hy, ?_⟩
    rw [hyc, dec8_mulVec, hcv]

end CFSG.Quasithin.H13.S8Cert
