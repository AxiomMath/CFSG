module

public import CFSG.Quasithin.H13.L32NG5Model
public import CFSG.Quasithin.H13.L32NS7Model3

public section

namespace CFSG.Quasithin.H13.G5Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert CFSG.Quasithin

@[expose] def MS (i : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (pSG ++ [mRepsS.getD i one8])

theorem ovB_spec :
    mRepsS.length = 2 ∧ (∀ r ∈ mRepsS, r ∈ gSE) ∧
      (∀ i ∈ [0, 1], (mES i).length = 48 ∧ subB (pSG ++ [mRepsS.getD i one8]) (mES i) = true) ∧
      ∀ y ∈ gSE, y ∈ elemsOf pSG ∨
        (49 ≤ (elemsOf (pSG ++ [y]) 49).length ∧ nodupB (elemsOf (pSG ++ [y]) 49) = true) ∨
        ((elemsOf (pSG ++ [y]) 49).length = 48 ∧ nodupB (elemsOf (pSG ++ [y]) 49) = true ∧
          ∃ i ∈ [0, 1], ∀ b ∈ elemsOf (pSG ++ [y]) 49, b ∈ mES i) := by
  have h := g5Check_parts.2.2.2.2.1
  simp only [ovB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_map] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  rcases h4 y hy with h | h | ⟨⟨h5, h6⟩, ⟨_, ⟨i, hi, rfl⟩, h7⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h5, h6, i, hi, fun b hb => ?_⟩)
    have := h7 b hb
    simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using this

theorem mRepS_mem {i : ℕ} (hi : i < 2) :
    mRepsS.getD i one8 ∈ gSE := by
  rw [List.getD_eq_getElem _ _ (by rw [ovB_spec.1]; exact hi)]
  exact ovB_spec.2.1 _ (List.getElem_mem _)

theorem MS_gens_mem {i : ℕ} (hi : i < 2) :
    ∀ g ∈ pSG ++ [mRepsS.getD i one8], g ∈ gSE := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact pB_spec.2.2.1 g hg
  · rw [List.mem_singleton.mp hg]; exact mRepS_mem hi

theorem MS_le_gS {i : ℕ} (hi : i < 2) : MS i ≤ g5 true true :=
  genSub_le_gS (MS_gens_mem hi)

theorem mES_spec {i : ℕ} (hi : i < 2) :
    (mES i).length = 48 ∧ subB (pSG ++ [mRepsS.getD i one8]) (mES i) = true :=
  ovB_spec.2.2.1 i (by interval_cases i <;> simp)

theorem mem_MS_iff {i : ℕ} (hi : i < 2) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ MS i ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ mES i :=
  mem_genSub_iff_of (mES_spec hi).2 (unit_of_gSE (MS_gens_mem hi)) u

theorem card_MS {i : ℕ} (hi : i < 2) : Nat.card (MS i) = 48 := by
  rw [MS, card_genSub_of (mES_spec hi).2 (unit_of_gSE (MS_gens_mem hi))]
  exact (mES_spec hi).1

theorem PS_le_MS (i : ℕ) : PS ≤ MS i :=
  Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem eq_MS_of {M : Subgroup (GL (Fin 8) (ZMod 2))}
    (hMs : M ≤ g5 true true) (hPM : PS ≤ M) (hcard : Nat.card M = 48) : ∃ i < 2, M = MS i := by
  obtain ⟨y, hyM, hyP⟩ : ∃ y ∈ M, y ∉ PS := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show M ≤ PS from h)
    rw [hcard, card_PS] at this
    omega
  set c := colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) with hc
  have hcs : c ∈ gSE := (mem_gS_iff y).mp (hMs hyM)
  have hcP : c ∉ elemsOf pSG := fun h => hyP ((mem_PS_iff y).mpr h)
  have hgens : ∀ g ∈ pSG ++ [c], g ∈ gSE := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact pB_spec.2.2.1 g hg
    · rw [List.mem_singleton.mp hg]; exact hcs
  have hval : ∀ g ∈ pSG ++ [c], Valid8 g := fun g hg =>
    (subB_spec basic_spec.1).1 _ (hgens g hg)
  have hle : genSub (pSG ++ [c]) ≤ M := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    rcases List.mem_append.mp hu with hu | hu
    · exact hPM (Subgroup.subset_closure hu)
    · have : u = y := eq_of_colsOf_eq (List.mem_singleton.mp hu)
      exact this ▸ hyM
  have hB : ∀ b ∈ elemsOf (pSG ++ [c]) 49,
      ∃ u ∈ M, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 b := by
    intro b hb
    obtain ⟨w, rfl⟩ := mem_elemsOf hb
    obtain ⟨u, hu, hu'⟩ := exists_evalW (pSG ++ [c]) hval (unit_of_gSE hgens) w
    exact ⟨u, hle hu, hu'⟩
  have hBval : ∀ b ∈ elemsOf (pSG ++ [c]) 49, Valid8 b := by
    intro b hb
    obtain ⟨w, rfl⟩ := mem_elemsOf hb
    exact valid8_evalW _ hval w
  rcases ovB_spec.2.2.2 c hcs with h | h | ⟨h48, hnd, i, hi, hsub⟩
  · exact absurd h hcP
  · have := le_card_of_list (nodup_of_nodupB h.2) hB hBval
    rw [hcard] at this
    omega
  · have hi2 : i < 2 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    refine ⟨i, hi2, ?_⟩
    have hBi : ∀ b ∈ elemsOf (pSG ++ [c]) 49,
        ∃ u ∈ M ⊓ MS i, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 b := by
      intro b hb
      obtain ⟨u, hu, hu'⟩ := hB b hb
      refine ⟨u, ⟨hu, (mem_MS_iff hi2 u).mpr ?_⟩, hu'⟩
      rw [hu', colsOf_dec8 (hBval b hb)]
      exact hsub b hb
    have hle48 := le_card_of_list (nodup_of_nodupB hnd) hBi hBval
    rw [h48] at hle48
    have hMi : M ≤ MS i := by
      have heq : M ⊓ MS i = M :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]; exact hle48)
      rw [← heq]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hMi (by rw [card_MS hi2, hcard])

@[expose] def OS (i : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (oddOf (mES i))

theorem oB_spec :
    ∀ i ∈ [0, 1], (oWsS.getD i (0, 0)).1 ≠ 0 ∧ (oWsS.getD i (0, 0)).2 ≠ 0 ∧
      (oWsS.getD i (0, 0)).1 ≠ (oWsS.getD i (0, 0)).2 ∧
      (∀ y ∈ oES i, mv8 y vS ^^^ vS ∈ [0, (oWsS.getD i (0, 0)).1, (oWsS.getD i (0, 0)).2,
        (oWsS.getD i (0, 0)).1 ^^^ (oWsS.getD i (0, 0)).2]) ∧
      (∃ y ∈ oES i, mv8 y vS ^^^ vS = (oWsS.getD i (0, 0)).1) ∧
      (∃ y ∈ oES i, mv8 y vS ^^^ vS = (oWsS.getD i (0, 0)).2) ∧
      (∀ w ∈ [(oWsS.getD i (0, 0)).1, (oWsS.getD i (0, 0)).2,
        (oWsS.getD i (0, 0)).1 ^^^ (oWsS.getD i (0, 0)).2], w ∈ eSpanS) ∧
      (∃ y ∈ oES i, ∃ v ∈ List.range 256, b5N (mv8 y v ^^^ v) (oWsS.getD i (0, 0)).1 = true) ∧
      subB (oddOf (mES i)) (oES i) = true ∧ (twoOf (oES i)).Nodup ∧
      (oES i).length = 3 * (twoOf (oES i)).length ∧
      (∀ a ∈ twoOf (oES i), ∀ b ∈ twoOf (oES i), mul8 a b ∈ twoOf (oES i)) ∧
      ∀ o ∈ oES i, pow4 (pow4 o) = one8 → pow4 o = one8 := by
  have h := g5Check_parts.2.2.2.2.2.1
  simp only [oB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  intro i hi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩, m⟩, n⟩, o⟩, p⟩ := h i hi
  refine ⟨by simpa using a, by simpa using b, by simpa using c, fun y hy => ?_, ?_, ?_,
    fun w hw => ?_, ?_, l, nodup_of_nodupB m, n, fun x hx y hy => ?_, fun y hy hy4 => ?_⟩
  · simpa [List.contains_iff_mem] using d y hy
  · simpa [List.any_eq_true] using e
  · simpa [List.any_eq_true] using f
  · simpa [List.contains_iff_mem] using g w hw
  · simpa [List.any_eq_true] using k
  · simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using o x hx y hy
  · have := p y hy
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at this
    exact this.resolve_left (not_not.mpr hy4)

theorem mem_zero_one {i : ℕ} (hi : i < 2) : i ∈ [0, 1] := by
  interval_cases i <;> simp

theorem OS_le_MS {i : ℕ} (hi : i < 2) : OS i ≤ MS i := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  exact (mem_MS_iff hi u).mpr (oddOf_sub _ hu)

theorem OS_gens_mem {i : ℕ} (hi : i < 2) :
    ∀ g ∈ oddOf (mES i), g ∈ gSE := by
  intro g hg
  have hgM := oddOf_sub g hg
  obtain ⟨w, rfl⟩ := mem_elemsOf hgM
  obtain ⟨u, hu, hu'⟩ := exists_evalW (pSG ++ [mRepsS.getD i one8])
    (subB_spec (mES_spec hi).2).2.2.2.2 (unit_of_gSE (MS_gens_mem hi)) w
  rw [← colsOf_dec8 (valid8_evalW _ (subB_spec (mES_spec hi).2).2.2.2.2 w), ← hu']
  exact (mem_gS_iff u).mp (MS_le_gS hi hu)

theorem mem_OS_iff {i : ℕ} (hi : i < 2) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ OS i ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ oES i :=
  mem_genSub_iff_of (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.2.1
    (unit_of_gSE (OS_gens_mem hi)) u

theorem oTwoUpper_MS {i : ℕ} (hi : i < 2) :
    oTwoUpper (MS i) = OS i := by
  unfold oTwoUpper OS genSub
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine List.mem_filter.mpr ⟨(mem_MS_iff hi u).mp h1, ?_⟩
    rw [beq_iff_eq, ← colsOf_pow3, (odd_orderOf_iff (card_MS hi) h1).mp h2, Units.val_one,
      colsOf_one]
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    have hu : u ∈ MS i := (mem_MS_iff hi u).mpr h1
    refine ⟨hu, (odd_orderOf_iff (card_MS hi) hu).mpr ?_⟩
    rw [beq_iff_eq, ← colsOf_pow3, ← colsOf_one, ← Units.val_one] at h2
    exact eq_of_colsOf_eq h2

theorem OS_vec {i : ℕ} (hi : i < 2) {y : GL (Fin 8) (ZMod 2)}
    (hy : y ∈ OS i) :
    (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vS) + vec8 vS ∈
      ({0, vec8 (oWsS.getD i (0, 0)).1, vec8 (oWsS.getD i (0, 0)).2,
        vec8 (oWsS.getD i (0, 0)).1 + vec8 (oWsS.getD i (0, 0)).2} : Set (Fin 8 → ZMod 2)) := by
  have hmem := (oB_spec i (mem_zero_one hi)).2.2.2.1 _ ((mem_OS_iff hi y).mp hy)
  rw [mulVec_vec8, ← vec8_xor (mv8 _ vS) vS]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> rw [h]
  · exact Or.inl vec8_zero
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (vec8_xor _ _)))

theorem exists_OS_of {i : ℕ} (hi : i < 2) {c : List ℕ}
    (hc : c ∈ oES i) : ∃ u ∈ OS i, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  have hsub := (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.2.1
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact exists_evalW _ (subB_spec hsub).2.2.2.2 (unit_of_gSE (OS_gens_mem hi)) w

theorem OS_vec_eq {i : ℕ} (hi : i < 2) :
    (∃ y ∈ OS i, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vS) + vec8 vS =
      vec8 (oWsS.getD i (0, 0)).1) ∧
    ∃ y ∈ OS i, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vS) + vec8 vS =
      vec8 (oWsS.getD i (0, 0)).2 := by
  have h := oB_spec i (mem_zero_one hi)
  constructor
  · obtain ⟨c, hc, hcw⟩ := h.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := exists_OS_of hi hc
    exact ⟨u, hu, by rw [hu', dec8_mulVec, ← vec8_xor, hcw]⟩
  · obtain ⟨c, hc, hcw⟩ := h.2.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := exists_OS_of hi hc
    exact ⟨u, hu, by rw [hu', dec8_mulVec, ← vec8_xor, hcw]⟩

theorem oWsS_ne {i : ℕ} (hi : i < 2) :
    vec8 (oWsS.getD i (0, 0)).1 ≠ 0 ∧ vec8 (oWsS.getD i (0, 0)).2 ≠ 0 ∧
      vec8 (oWsS.getD i (0, 0)).1 ≠ vec8 (oWsS.getD i (0, 0)).2 := by
  interval_cases i <;> decide

theorem oWsS_mem {i : ℕ} (hi : i < 2)
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ p ∈ eWS, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) :
    vec8 (oWsS.getD i (0, 0)).1 ∈ W ∧ vec8 (oWsS.getD i (0, 0)).2 ∈ W := by
  have h := (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.1
  exact ⟨eSpanS_mem W hW _ (h _ (by simp)), eSpanS_mem W hW _ (h _ (by simp))⟩

theorem OS_b5 {i : ℕ} (hi : i < 2) :
    ∃ y ∈ OS i, ∃ v : ℕ, b5V ((y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 v) + vec8 v)
      (vec8 (oWsS.getD i (0, 0)).1) = 1 := by
  obtain ⟨c, hc, v, -, hv⟩ := (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.1
  obtain ⟨u, hu, hu'⟩ := exists_OS_of hi hc
  refine ⟨u, hu, v, ?_⟩
  rw [hu', dec8_mulVec, ← vec8_xor, ← b5N_spec, hv]
  rfl

theorem OS_ne : OS 0 ≠ OS 1 := by
  intro h
  obtain ⟨y, hy, hyw⟩ := (OS_vec_eq (i := 0) (by norm_num)).1
  have := OS_vec (i := 1) (by norm_num) (h ▸ hy)
  rw [hyw] at this
  revert this
  decide

@[expose] def RS (i : ℕ) (hi : i < 2) :
    Subgroup (GL (Fin 8) (ZMod 2)) where
  carrier := {u | colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oES i)}
  one_mem' := by
    show colsOf ((1 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oES i)
    rw [Units.val_one, colsOf_one]
    exact List.mem_filter.mpr
      ⟨(subB_spec (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.2.1).2.2.2.1, by decide⟩
  mul_mem' := fun {a b} ha hb => by
    show colsOf ((a * b : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oES i)
    rw [Units.val_mul, colsOf_mul]
    exact (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.2.2.2.2.1 _ ha _ hb
  inv_mem' := fun {a} ha => by
    show colsOf ((a⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oES i)
    have h4 : a ^ 4 = 1 := by
      have := (List.mem_filter.mp ha).2
      rw [beq_iff_eq, ← colsOf_pow4, ← colsOf_one, ← Units.val_one] at this
      exact eq_of_colsOf_eq this
    have hinv : a⁻¹ = a * (a * a) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv,
        show a * (a * a) * a = a ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc], h4]
    rw [hinv, Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul]
    have hc := (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.2.2.2.2.1
    exact hc _ ha _ (hc _ ha _ ha)

theorem RS_le_OS {i : ℕ} (hi : i < 2) : RS i hi ≤ OS i :=
  fun u hu => (mem_OS_iff hi u).mpr (List.mem_filter.mp hu).1

theorem pow_four_of_RS {i : ℕ} (hi : i < 2)
    {u : GL (Fin 8) (ZMod 2)} (hu : u ∈ RS i hi) : u ^ 4 = 1 := by
  have := (List.mem_filter.mp hu).2
  rw [beq_iff_eq, ← colsOf_pow4, ← colsOf_one, ← Units.val_one] at this
  exact eq_of_colsOf_eq this

theorem card_OS_eq {i : ℕ} (hi : i < 2) :
    Nat.card (OS i) = 3 * Nat.card (RS i hi) := by
  have h := oB_spec i (mem_zero_one hi)
  have hsub := subB_spec h.2.2.2.2.2.2.2.2.1
  have hO : Nat.card (OS i) = (oES i).length :=
    card_genSub_of h.2.2.2.2.2.2.2.2.1 (unit_of_gSE (OS_gens_mem hi))
  have hR : Nat.card (RS i hi) = (twoOf (oES i)).length := by
    refine card_of_cols (fun u => Iff.rfl) h.2.2.2.2.2.2.2.2.2.1
      (fun x hx => hsub.1 x (List.mem_filter.mp hx).1) fun x hx => ?_
    obtain ⟨u, -, hu⟩ := exists_OS_of hi (List.mem_filter.mp hx).1
    exact ⟨u, hu⟩
  rw [hO, hR]
  exact h.2.2.2.2.2.2.2.2.2.2.1

theorem RS_normal {i : ℕ} (hi : i < 2) :
    ((RS i hi).subgroupOf (OS i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hgn : ((g * n * g⁻¹ : ↥(OS i)) : GL (Fin 8) (ZMod 2)) ∈ OS i := (g * n * g⁻¹).2
  have h4 : ((g * n * g⁻¹ : ↥(OS i)) : GL (Fin 8) (ZMod 2)) ^ 4 = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, pow_four_of_RS hi hn, mul_one, mul_inv_cancel]
  refine List.mem_filter.mpr ⟨(mem_OS_iff hi _).mp hgn, ?_⟩
  rw [beq_iff_eq, ← colsOf_pow4, h4, Units.val_one, colsOf_one]

theorem RS_isPGroup {i : ℕ} (hi : i < 2) :
    IsPGroup 2 ↥((RS i hi).subgroupOf (OS i)) := by
  rintro ⟨⟨u, huO⟩, hu⟩
  refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
  simpa using pow_four_of_RS hi (Subgroup.mem_subgroupOf.mp hu)

theorem pCore_OS {i : ℕ} (hi : i < 2) :
    CFSG.Open.pCore 2 ↥(OS i) = (RS i hi).subgroupOf (OS i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun x hx => ?_)
    (CFSG.LieType.BorelTits.le_pCore 2 (RS_normal hi) (RS_isPGroup hi))
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(OS i)) (r := 2)) ⟨x, hx⟩
  have hxn : (x : GL (Fin 8) (ZMod 2)) ^ 2 ^ n = 1 := by
    have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥(OS i)) => ((y : ↥(OS i)) :
      GL (Fin 8) (ZMod 2))) hn
    simpa using this
  have hxM : (x : GL (Fin 8) (ZMod 2)) ∈ MS i := OS_le_MS hi x.2
  have h48 : orderOf (x : GL (Fin 8) (ZMod 2)) ∣ 48 := by
    rw [← card_MS hi, ← Subgroup.orderOf_mk _ hxM]
    exact orderOf_dvd_natCard _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxn)
  have h16 : orderOf (x : GL (Fin 8) (ZMod 2)) ∣ 16 := by
    rw [hk] at h48 ⊢
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact hc.dvd_of_dvd_mul_right (by simpa using h48)
  have hx16 : (x : GL (Fin 8) (ZMod 2)) ^ 16 = 1 := orderOf_dvd_iff_pow_eq_one.mp h16
  rw [Subgroup.mem_subgroupOf]
  have hc := (mem_OS_iff hi _).mp x.2
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  rw [beq_iff_eq]
  refine (oB_spec i (mem_zero_one hi)).2.2.2.2.2.2.2.2.2.2.2.2 _ hc ?_
  rw [← colsOf_pow16, hx16, Units.val_one, colsOf_one]

theorem index_pCore_OS {i : ℕ} (hi : i < 2) :
    (CFSG.Open.pCore 2 ↥(OS i)).index = 3 := by
  rw [pCore_OS hi]
  have h := Subgroup.relIndex_mul_card (RS i hi) (OS i)
  rw [inf_eq_left.mpr (RS_le_OS hi), card_OS_eq hi] at h
  have hpos : 0 < Nat.card (RS i hi) := Nat.card_pos
  unfold Subgroup.relIndex at h
  nlinarith

theorem OS_sup_PS {i : ℕ} (hi : i < 2) : OS i ⊔ PS = MS i := by
  have hle : OS i ⊔ PS ≤ MS i := sup_le (OS_le_MS hi) (PS_le_MS i)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_MS hi]
  have h3 : 3 ∣ Nat.card ↥(OS i ⊔ PS) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : OS i ≤ OS i ⊔ PS)
    rw [card_OS_eq hi] at this
    exact (Dvd.intro _ rfl).trans this
  have h16 : 16 ∣ Nat.card ↥(OS i ⊔ PS) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : PS ≤ OS i ⊔ PS)
    rwa [card_PS] at this
  have h48 : 48 ∣ Nat.card ↥(OS i ⊔ PS) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 16) h3 h16
  exact Nat.le_of_dvd Nat.card_pos h48

@[expose] def M12S : Subgroup (GL (Fin 8) (ZMod 2)) :=
  genSub (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8])

theorem m12B_spec :
    subB (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8]) m12ES = true ∧
    (∀ x ∈ m12ES, blkPerm blkSA x ∈ perm3L ∧ blkPerm blkSB x ∈ perm3L) ∧
    (∀ x ∈ m12ES, ∀ y ∈ m12ES,
      blkPerm blkSA (mul8 x y) = compL (blkPerm blkSA x) (blkPerm blkSA y) ∧
        blkPerm blkSB (mul8 x y) = compL (blkPerm blkSB x) (blkPerm blkSB y)) ∧
    (∀ l ∈ perm3L, ∀ l' ∈ perm3L, ∃ x ∈ m12ES, blkPerm blkSA x = l ∧ blkPerm blkSB x = l') ∧
    ∀ x ∈ m12ES, blkPerm blkSA x = [0, 1, 2] → blkPerm blkSB x = [0, 1, 2] →
      mul8 x x = one8 := by
  have h := g5Check_parts.2.2.2.2.2.2
  simp only [m12B, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  refine ⟨a, fun x hx => ?_, c, fun l hl l' hl' => ?_, fun x hx h1 h2 => ?_⟩
  · simpa [List.contains_iff_mem] using b x hx
  · simpa [List.any_eq_true] using d l hl l' hl'
  · have := e x hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact absurd h1 h
    · exact absurd h2 h
    · exact h

theorem M12S_gens_mem :
    ∀ g ∈ pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8], g ∈ gSE := by
  intro g hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl
  · exact pB_spec.2.2.1 g hg
  · exact mRepS_mem (by norm_num)
  · exact mRepS_mem (by norm_num)

theorem mem_M12S_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ M12S ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ m12ES :=
  mem_genSub_iff_of m12B_spec.1 (unit_of_gSE M12S_gens_mem) u

theorem sup_MS : MS 0 ⊔ MS 1 = M12S := by
  apply le_antisymm
  · refine sup_le (Subgroup.closure_mono fun u hu => ?_) (Subgroup.closure_mono fun u hu => ?_)
    · simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hu ⊢
      tauto
    · simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hu ⊢
      tauto
  · refine (Subgroup.closure_le _).mpr fun u hu => ?_
    simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    rcases hu with hu | hu | hu
    · exact Subgroup.mem_sup_left (PS_le_MS 0 (Subgroup.subset_closure hu))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [hu]))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [hu]))

theorem blkPermS_one : blkPerm blkSA one8 = [0, 1, 2] ∧ blkPerm blkSB one8 = [0, 1, 2] := by
  decide

@[expose] noncomputable def chiS :
    ↥M12S →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) where
  toFun x := (toPerm3 (blkPerm blkSA (colsOf ((x : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)))),
    toPerm3 (blkPerm blkSB (colsOf ((x : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)))))
  map_one' := by
    simp only [OneMemClass.coe_one, Units.val_one, colsOf_one, blkPermS_one.1, blkPermS_one.2]
    rfl
  map_mul' x y := by
    have hx := (mem_M12S_iff _).mp x.2
    have hy := (mem_M12S_iff _).mp y.2
    simp only [Subgroup.coe_mul, Units.val_mul, colsOf_mul, (m12B_spec.2.2.1 _ hx _ hy).1,
      (m12B_spec.2.2.1 _ hx _ hy).2,
      toPerm3_mul _ (m12B_spec.2.1 _ hx).1 _ (m12B_spec.2.1 _ hy).1,
      toPerm3_mul _ (m12B_spec.2.1 _ hx).2 _ (m12B_spec.2.1 _ hy).2, Prod.mk_mul_mk]

theorem chiS_surjective : Function.Surjective chiS := by
  rintro ⟨σ, τ⟩
  obtain ⟨l, hl, rfl⟩ := toPerm3_surj σ
  obtain ⟨l', hl', rfl⟩ := toPerm3_surj τ
  obtain ⟨c, hc, hca, hcb⟩ := m12B_spec.2.2.2.1 l hl l' hl'
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  obtain ⟨u, hu, hu'⟩ := exists_evalW (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8])
    (subB_spec m12B_spec.1).2.2.2.2 (unit_of_gSE M12S_gens_mem) w
  have hcu : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      evalW (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8]) w := by
    rw [hu', colsOf_dec8 (valid8_evalW (pSG ++ [mRepsS.getD 0 one8, mRepsS.getD 1 one8])
      (subB_spec m12B_spec.1).2.2.2.2 w)]
  refine ⟨⟨u, hu⟩, ?_⟩
  show (toPerm3 (blkPerm blkSA (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))),
    toPerm3 (blkPerm blkSB (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))))) = _
  rw [hcu, hca, hcb]

theorem sq_eq_one_of_chiS {x : ↥M12S} (h : chiS x = 1) :
    (x : GL (Fin 8) (ZMod 2)) * x = 1 := by
  have hx := (mem_M12S_iff _).mp x.2
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change toPerm3 (blkPerm blkSA (colsOf ((x : GL (Fin 8) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2)))) = 1 at h1
  change toPerm3 (blkPerm blkSB (colsOf ((x : GL (Fin 8) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2)))) = 1 at h2
  have hsq := m12B_spec.2.2.2.2 _ hx (toPerm3_eq_one _ (m12B_spec.2.1 _ hx).1 h1)
    (toPerm3_eq_one _ (m12B_spec.2.1 _ hx).2 h2)
  apply eq_of_colsOf_eq
  rw [Units.val_mul, colsOf_mul, hsq, Units.val_one, colsOf_one]

theorem M12S_eq : M12S = OS 0 ⊔ OS 1 ⊔ PS := by
  rw [← sup_MS, ← OS_sup_PS (i := 0) (by norm_num), ← OS_sup_PS (i := 1) (by norm_num)]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right)

end CFSG.Quasithin.H13.G5Cert
