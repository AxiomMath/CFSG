module

public import CFSG.Quasithin.H13.L32NM22Model

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert L1442M

theorem unit_of_pE {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ pE) :
    ∀ g ∈ gens, ∃ u : GL (Fin 12) (ZMod 2), (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_PM (h g hg); ⟨u, hu⟩

theorem PM_le_m22 : PM ≤ m22 := PM_le_S0.trans S0_le

theorem PM_fix {p : GL (Fin 12) (ZMod 2)} (hp : p ∈ PM) :
    (p : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0 :=
  S0_fix (PM_le_S0 hp)

theorem eq_of_fixed_PM (v : Fin 12 → ZMod 2)
    (hv : ∀ γ ∈ PM, (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = vecN 12 v0 := by
  have hval := (subB_spec pB_spec.1).2.2.2.2
  have hfix : ∀ p ∈ pG, mvN p (codeN v) = codeN v := by
    intro p hp
    obtain ⟨u, hu⟩ := pG_unit' p hp
    have := hv u (mem_genSubN_of_mem hval hp hu)
    rw [← vecN_codeN v, hu, decN_mulVec (hval p hp).1] at this
    exact vecN_inj (mvN_lt (hval p hp).2 _) (codeN_lt v) (by rw [this, vecN_codeN])
  rcases pB_spec.2.2 (codeN v) (codeN_lt v) hfix with h | h
  · left
    rw [← vecN_codeN v, h, vecN_zero]
  · right
    rw [← vecN_codeN v, h]

@[expose] def E0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 e0G

theorem e0B_spec :
    subB 12 e0G e0E = true ∧ e0E.length = 32 ∧ (∀ g ∈ e0G, g ∈ pE) ∧
      (∀ c ∈ cjL, mulN c.1 c.2 = one12) ∧
      ∀ x ∈ pE, x ∈ e0E ∨ ∃ c ∈ cjL, mulN (mulN c.1 x) c.2 ∉ pE := by
  have h := m22Check_parts.2.2.2.2.2.1
  simp only [e0B, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx => ?_⟩
  rcases h5 x hx with h6 | ⟨c, hc, h6⟩
  · exact Or.inl h6
  · exact Or.inr ⟨c, hc, fun h7 => h6 (by simpa [Std.HashSet.contains_ofList] using h7)⟩

theorem e0G_mem : ∀ g ∈ e0G, g ∈ pE := e0B_spec.2.2.1

theorem mem_E0_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ E0 ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ e0E :=
  mem_genSubN_iff_of e0B_spec.1 (unit_of_pE e0G_mem) u

theorem card_E0 : Nat.card E0 = 32 := by
  rw [E0, card_genSubN_of e0B_spec.1 (unit_of_pE e0G_mem)]
  exact e0B_spec.2.1

theorem validN_powN {x : List ℕ} (hx : ValidN 12 x) (k : ℕ) : ValidN 12 (powN 12 x k) := by
  induction k with
  | zero => exact validN_oneN
  | succ k ih => exact validN_mulN hx ih

theorem validN_gInv : ∀ g ∈ gInv, ValidN 12 g := by
  intro g hg
  simp only [gInv, List.mem_cons, List.not_mem_nil, or_false] at hg
  have h0 : ValidN 12 (gG.getD 0 []) := by
    rw [List.getD_eq_getElem _ _ (by simp [gG])]
    exact validN_gG _ (List.getElem_mem _)
  have h1 : ValidN 12 (gG.getD 1 []) := by
    rw [List.getD_eq_getElem _ _ (by simp [gG])]
    exact validN_gG _ (List.getElem_mem _)
  rcases hg with rfl | rfl
  · exact h0
  · exact validN_powN h1 3

theorem validN_cjL : ∀ c ∈ cjL, ValidN 12 c.1 ∧ ValidN 12 c.2 := by
  intro c hc
  simp only [cjL, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨w, -, rfl⟩ | ⟨w, -, rfl⟩
  · exact ⟨validN_evalW gG validN_gG w, validN_evalW gInv validN_gInv _⟩
  · exact ⟨validN_evalW gInv validN_gInv _, validN_evalW gG validN_gG w⟩

theorem exists_S0_of_cjL {c : List ℕ × List ℕ} (hc : c ∈ cjL) :
    ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.1 := by
  have hgen : ∀ w ∈ s0W, tU w ∈ S0 := fun w hw => Subgroup.subset_closure (by
    change colsN ((tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ s0G
    rw [tU_val, colsN_decN (validN_evalW gG validN_gG w)]
    exact List.mem_map_of_mem hw)
  have hc' := hc
  simp only [cjL, List.mem_append, List.mem_map] at hc'
  rcases hc' with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact ⟨tU w, hgen w hw, tU_val w⟩
  · have hm : (tW w, evalW 12 gInv w.reverse) ∈ cjL :=
      List.mem_append_left _ (List.mem_map_of_mem hw)
    exact ⟨(tU w)⁻¹, S0.inv_mem (hgen w hw), inv_val_of (validN_evalW gG validN_gG w)
      (validN_evalW gInv validN_gInv _) (tU_val w) (e0B_spec.2.2.2.1 _ hm)⟩

theorem le_E0_of {W : Subgroup (GL (Fin 12) (ZMod 2))}
    (hWP : W ≤ PM) (hnorm : ∀ ν ∈ S0, ∀ x ∈ W, ν * x * ν⁻¹ ∈ W) : W ≤ E0 := by
  intro x hx
  rw [mem_E0_iff]
  have hxP := (mem_PM_iff x).mp (hWP hx)
  rcases e0B_spec.2.2.2.2 _ hxP with h | ⟨c, hc, hout⟩
  · exact h
  · exfalso
    have hcc := e0B_spec.2.2.2.1 c hc
    obtain ⟨hv1, hv2⟩ := validN_cjL c hc
    obtain ⟨u, hu, hu'⟩ := exists_S0_of_cjL hc
    have hinv := inv_val_of hv1 hv2 hu' hcc
    have hmem := hWP (hnorm u hu x hx)
    rw [mem_PM_iff, Units.val_mul, Units.val_mul, colsN_mul, colsN_mul, hu', hinv,
      colsN_decN hv1, colsN_decN hv2] at hmem
    exact hout hmem

theorem eq_E0_of {W : Subgroup (GL (Fin 12) (ZMod 2))}
    (hWP : W ≤ PM) (hnorm : ∀ ν ∈ S0, ∀ x ∈ W, ν * x * ν⁻¹ ∈ W) (hcard : Nat.card W = 32) :
    W = E0 :=
  Subgroup.eq_of_le_of_card_ge (le_E0_of hWP hnorm) (by rw [card_E0, hcard])

theorem q12c_eq : decN 12 q12c = q12 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem polN_q12 (v w : ℕ) :
    Mat8Cert.b2z (polN 12 q12c v w) = polV q12 (vecN 12 v) (vecN 12 w) := by
  rw [polN_spec (by rfl : q12c.length = 12), q12c_eq]

theorem witB_spec :
    ∀ p ∈ wits, p.2.1 ∈ e0E ∧ polN 12 q12c p.2.2 v0 = false ∧ mvN p.2.1 p.2.2 ^^^ p.2.2 = p.1 := by
  have h := m22Check_parts.2.2.2.2.2.2.1
  simp only [witB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true'] at h
  intro p hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := h p hp
  exact ⟨h1, h2, h3⟩

theorem ovB_spec :
    (∀ uw ∈ orbL, uw.1 = v0 ∨ uw.1 ∈ U4 ∨ ∃ p₁ ∈ pE, ∃ p₂ ∈ pE, mvN p₁ uw.1 ≠ uw.1 ∧
      mvN p₂ uw.1 ≠ uw.1 ∧ mvN p₂ uw.1 ≠ mvN p₁ uw.1) ∧
    (∀ r ∈ rP, (∃ w, r.1 = evalW 12 s0G w) ∧ mulN r.1 r.2 = one12) ∧
    (rP.length = 15 ∧
      ∀ i < 15, ∀ j < i, mulN (rP.getD j ([], [])).2 (rP.getD i ([], [])).1 ∉ pE) ∧
    (∀ uw ∈ orbL, uw.1 ∈ U4 → ∀ r ∈ rP,
      (mulN (tW uw.2) r.1 ∈ mE 0 ∨ mulN (tW uw.2) r.1 ∈ mE 1) ∨
        ovFourB (Std.HashSet.ofList pE) (mulN (tW uw.2) r.1) = true) ∧
    ∀ i ∈ [0, 1], (mE i).Nodup ∧ (mE i).length = 768 ∧ (mCosP i).length = 3 ∧
      (∀ c ∈ mCosP i, ValidN 12 c.2 ∧ mulN c.1 c.2 = one12) ∧ (∃ c ∈ mCosP i, mulN c.2 one12 ∈ pE) ∧
      ∀ g ∈ pG ++ [mRep.getD i one12], ∀ c ∈ mCosP i, ∃ c' ∈ mCosP i,
        mulN c'.2 (mulN g c.1) ∈ pE := by
  have h := m22Check_parts.2.2.2.2.2.2.2.1
  simp only [ovB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2a, h2b⟩, h3a, h3b⟩, h4⟩, h5⟩ := h
  refine ⟨fun uw huw => ?_, fun r hr => ?_, ⟨by simpa using h3a, fun i hi j hj => ?_⟩,
    fun uw huw hU r hr => ?_, fun i hi => ?_⟩
  · have := h1 uw huw
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, List.any_eq_true,
      Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with (h | h) | ⟨p₁, hp₁, h6, p₂, hp₂, h7, h8⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨p₁, hp₁, p₂, hp₂, h6, h7, h8⟩)
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
    have hlen : rP.length = 15 := by simpa using h3a
    have h6 := h2a n (List.mem_range.mpr (by omega))
    rw [List.getD_eq_getElem _ _ hn] at h6
    simp only [beq_iff_eq] at h6
    have h7 := h2b _ (List.getElem_mem hn)
    simp only [beq_iff_eq] at h7
    exact ⟨⟨_, h6⟩, h7⟩
  · have := h3b i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
    simpa [Std.HashSet.contains_ofList] using this
  · have := h4 uw huw
    have hc : U4.contains uw.1 = true := List.contains_iff_mem.mpr hU
    simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    have := this r hr
    simp only [Bool.or_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem] at this
    exact this
  · have := h5 i hi
    simp only [beq_iff_eq, Bool.and_eq_true, List.any_eq_true, Std.HashSet.contains_ofList,
      List.contains_iff_mem] at this
    obtain ⟨⟨⟨⟨⟨hn, hl⟩, hc⟩, hv⟩, ho⟩, hg⟩ := this
    exact ⟨nodup_of_nodupB hn, hl, hc, fun c hc' => ⟨validB_iff.mp (hv c hc').1, (hv c hc').2⟩,
      ho, hg⟩

@[expose] def Mi (i : ℕ) : Subgroup (GL (Fin 12) (ZMod 2)) :=
  genSubN 12 (pG ++ [mRep.getD i one12])

theorem rP_mem_four : rP.getD 4 ([], []) ∈ rP := by
  rw [List.getD_eq_getElem _ _ (by decide)]
  exact List.getElem_mem _

theorem rP_mem_eleven : rP.getD 11 ([], []) ∈ rP := by
  rw [List.getD_eq_getElem _ _ (by decide)]
  exact List.getElem_mem _

theorem mRep_unit {i : ℕ} (hi : i < 2) :
    ∃ u ∈ m22, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (mRep.getD i one12) := by
  have key : ∀ (w : List ℕ) (r : List ℕ × List ℕ), r ∈ rP →
      ∃ u ∈ m22, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (mulN (tW w) r.1) := by
    intro w r hr
    obtain ⟨rU, hrU, hrU'⟩ := exists_S0_of_rP hr
    refine ⟨tU w * rU, m22.mul_mem (tU_mem w) (S0_le hrU), ?_⟩
    rw [Units.val_mul, tU_val, hrU', decN_mulN (length_evalW gG w) (validN_rP r hr).1.1]
  interval_cases i
  · exact key _ _ rP_mem_four
  · exact key _ _ rP_mem_eleven

theorem Mi_gens_unit {i : ℕ} (hi : i < 2) :
    ∀ g ∈ pG ++ [mRep.getD i one12], ∃ u ∈ m22,
      (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨u, hu, hu'⟩ := pG_unit g hg
    exact ⟨u, S0_le hu, hu'⟩
  · rw [List.mem_singleton.mp hg]
    exact mRep_unit hi

theorem mE_spec {i : ℕ} (hi : i < 2) :
    (mE i).Nodup ∧ (mE i).length = 768 ∧ (mCosP i).length = 3 ∧
      (∀ c ∈ mCosP i, ValidN 12 c.2 ∧ mulN c.1 c.2 = one12) ∧ (∃ c ∈ mCosP i, mulN c.2 one12 ∈ pE) ∧
      ∀ g ∈ pG ++ [mRep.getD i one12], ∀ c ∈ mCosP i, ∃ c' ∈ mCosP i,
        mulN c'.2 (mulN g c.1) ∈ pE :=
  ovB_spec.2.2.2.2 i (by interval_cases i <;> simp)

theorem validN_mRep {i : ℕ} (hi : i < 2) : ValidN 12 (mRep.getD i one12) := by
  interval_cases i
  · exact validN_mulN (validN_evalW gG validN_gG _) (validN_rP _ rP_mem_four).1
  · exact validN_mulN (validN_evalW gG validN_gG _) (validN_rP _ rP_mem_eleven).1

theorem Mi_gens_valid {i : ℕ} (hi : i < 2) : ∀ g ∈ pG ++ [mRep.getD i one12], ValidN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (subB_spec pB_spec.1).2.2.2.2 g hg
  · rw [List.mem_singleton.mp hg]
    exact validN_mRep hi

theorem Mi_gens_unit' {i : ℕ} (hi : i < 2) :
    ∀ g ∈ pG ++ [mRep.getD i one12], ∃ u : GL (Fin 12) (ZMod 2),
      (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := Mi_gens_unit hi g hg; ⟨u, hu⟩

theorem exists_mem_Mi {i : ℕ} (hi : i < 2) {c : List ℕ} (hc : c ∈ mE i) :
    ∃ u ∈ Mi i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact exists_evalW _ (Mi_gens_valid hi) (Mi_gens_unit' hi) w

theorem validN_mE {i : ℕ} (hi : i < 2) : ∀ c ∈ mE i, ValidN 12 c := by
  intro c hc
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact validN_evalW _ (Mi_gens_valid hi) w

theorem mCosP_unit {i : ℕ} (hi : i < 2) {c : List ℕ × List ℕ} (hc : c ∈ mCosP i) :
    ValidN 12 c.1 ∧ ∃ u ∈ Mi i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.1 ∧
      ((u⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.2 := by
  have hv := (mE_spec hi).2.2.2.1 c hc
  have hz : c ∈ ([[], [5], [0, 5]].map (evalW 12 (pG ++ [mRep.getD i one12]))).zip
      (mInv.getD i []) := hc
  obtain ⟨w, -, hw⟩ := List.mem_map.mp (List.of_mem_zip hz).1
  obtain ⟨u, hu, hu'⟩ := exists_evalW _ (Mi_gens_valid hi) (Mi_gens_unit' hi) w
  have hv1 : ValidN 12 c.1 := by
    rw [← hw]
    exact validN_evalW _ (Mi_gens_valid hi) w
  have hu1 : (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.1 := by
    rw [← hw]
    exact hu'
  exact ⟨hv1, u, hu, hu1, inv_val_of hv1 hv.1 hu1 hv.2⟩

theorem exists_mCosP_of_mem_Mi {i : ℕ} (hi : i < 2) {u : GL (Fin 12) (ZMod 2)} (hu : u ∈ Mi i) :
    ∃ c ∈ mCosP i, mulN c.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
  obtain ⟨-, -, -, hv, ho, hg⟩ := mE_spec hi
  have key : ∀ c ∈ mCosP i, ∀ cu : GL (Fin 12) (ZMod 2),
      ((cu⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.2 →
      ∀ y : GL (Fin 12) (ZMod 2),
        (cu⁻¹ * y ∈ PM ↔ mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) := by
    intro c hc cu hcu y
    rw [mem_PM_iff, Units.val_mul, colsN_mul, hcu, colsN_decN (hv c hc).1]
  have hstep : ∀ s : GL (Fin 12) (ZMod 2),
      colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ pG ++ [mRep.getD i one12] →
      ∀ y : GL (Fin 12) (ZMod 2),
        (∃ c ∈ mCosP i, mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) →
        ∃ c ∈ mCosP i, mulN c.2
          (colsN ((s * y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
    rintro s hs y ⟨c, hc, hcy⟩
    obtain ⟨c', hc', hc's⟩ := hg _ hs c hc
    obtain ⟨hv1, cu, -, hcu1, hcu2⟩ := mCosP_unit hi hc
    obtain ⟨-, cu', -, -, hcu'2⟩ := mCosP_unit hi hc'
    refine ⟨c', hc', (key c' hc' cu' hcu'2 _).mp ?_⟩
    have e : cu'⁻¹ * (s * y) = (cu'⁻¹ * (s * cu)) * (cu⁻¹ * y) := by group
    rw [e]
    refine PM.mul_mem ((key c' hc' cu' hcu'2 _).mpr ?_) ((key c hc cu hcu2 y).mpr hcy)
    rw [Units.val_mul, colsN_mul, hcu1, colsN_decN hv1]
    exact hc's
  have hpow : ∀ s : GL (Fin 12) (ZMod 2),
      colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ pG ++ [mRep.getD i one12] → ∀ (m : ℕ)
      (y : GL (Fin 12) (ZMod 2)),
      (∃ c ∈ mCosP i, mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) →
      ∃ c ∈ mCosP i, mulN c.2
        (colsN ((s ^ m * y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
    intro s hs m
    induction m with
    | zero =>
      intro y hy
      rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep s hs _ (ih y hy)
  unfold Mi genSubN at hu
  refine Subgroup.closure_induction_left (p := fun (u : GL (Fin 12) (ZMod 2)) _ =>
    ∃ c ∈ mCosP i, mulN c.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) ?_ ?_ ?_ hu
  · rw [Units.val_one, colsN_one]
    exact ho
  · intro s hs y _ hy
    exact hstep s hs y hy
  · intro s hs y _ hy
    have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s
    have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow s hs _ y hy

theorem card_Mi_le {i : ℕ} (hi : i < 2) : Nat.card (Mi i) ≤ 768 := by
  classical
  have hv := (mE_spec hi).2.2.2.1
  have hex : ∀ c : {c // c ∈ mCosP i}, ∃ cu : GL (Fin 12) (ZMod 2),
      ((cu⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.1.2 :=
    fun c => let ⟨_, cu, _, _, h⟩ := mCosP_unit hi c.2; ⟨cu, h⟩
  let cu : {c // c ∈ mCosP i} → GL (Fin 12) (ZMod 2) := fun c => Classical.choose (hex c)
  have hcu : ∀ c, (((cu c)⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      decN 12 c.1.2 := fun c => Classical.choose_spec (hex c)
  have hsel : ∀ u : Mi i, ∃ c : {c // c ∈ mCosP i}, (cu c)⁻¹ * (u : GL (Fin 12) (ZMod 2)) ∈ PM := by
    intro u
    obtain ⟨c, hc, h⟩ := exists_mCosP_of_mem_Mi hi u.2
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [mem_PM_iff, Units.val_mul, colsN_mul, hcu, colsN_decN (hv c hc).1]
    exact h
  let f : Mi i → {c // c ∈ mCosP i} × PM := fun u =>
    (Classical.choose (hsel u), ⟨_, Classical.choose_spec (hsel u)⟩)
  have hf : Function.Injective f := by
    intro u v h
    have h1 : Classical.choose (hsel u) = Classical.choose (hsel v) := congrArg Prod.fst h
    have h2 : (cu (Classical.choose (hsel u)))⁻¹ * (u : GL (Fin 12) (ZMod 2)) =
        (cu (Classical.choose (hsel v)))⁻¹ * (v : GL (Fin 12) (ZMod 2)) :=
      congrArg (fun x => ((x.2 : PM) : GL (Fin 12) (ZMod 2))) h
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have h3 : Nat.card {c // c ∈ mCosP i} ≤ 3 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (List.mem_toFinset (l := mCosP i) (a := x)).symm), Nat.card_eq_fintype_card, Fintype.card_coe,
      ← (mE_spec hi).2.2.1]
    exact List.toFinset_card_le _
  have h4 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_PM] at h4
  omega

theorem mem_Mi_iff {i : ℕ} (hi : i < 2) (u : GL (Fin 12) (ZMod 2)) :
    u ∈ Mi i ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ mE i := by
  classical
  obtain ⟨hnd, hlen, -⟩ := mE_spec hi
  constructor
  · intro hu
    let g : {b // b ∈ mE i} → Mi i := fun b =>
      ⟨Classical.choose (exists_mem_Mi hi b.2), (Classical.choose_spec (exists_mem_Mi hi b.2)).1⟩
    have hg : Function.Injective g := by
      intro b b' h
      have h1 : ((Classical.choose (exists_mem_Mi hi b.2) : GL (Fin 12) (ZMod 2)) :
          Matrix (Fin 12) (Fin 12) (ZMod 2)) =
          ((Classical.choose (exists_mem_Mi hi b'.2) : GL (Fin 12) (ZMod 2)) :
            Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
        congrArg (fun v : Mi i =>
          ((v : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) h
      rw [(Classical.choose_spec (exists_mem_Mi hi b.2)).2,
        (Classical.choose_spec (exists_mem_Mi hi b'.2)).2] at h1
      exact Subtype.ext (decN_injOn (validN_mE hi _ b.2) (validN_mE hi _ b'.2) h1)
    have hcard : Nat.card {b // b ∈ mE i} = 768 := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        (List.mem_toFinset (l := mE i) (a := x)).symm), Nat.card_eq_fintype_card,
        Fintype.card_coe, List.toFinset_card_of_nodup hnd, hlen]
    obtain ⟨b, hb⟩ := (hg.bijective_of_nat_card_le (by rw [hcard]; exact card_Mi_le hi)).2 ⟨u, hu⟩
    have h1 : ((Classical.choose (exists_mem_Mi hi b.2) : GL (Fin 12) (ZMod 2)) :
        Matrix (Fin 12) (Fin 12) (ZMod 2)) = (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
      congrArg (fun v : Mi i => ((v : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) hb
    rw [(Classical.choose_spec (exists_mem_Mi hi b.2)).2] at h1
    rw [← h1, colsN_decN (validN_mE hi _ b.2)]
    exact b.2
  · intro hu
    obtain ⟨v, hv, hv'⟩ := exists_mem_Mi hi hu
    rw [decN_colsN] at hv'
    have : u = v := Units.ext hv'.symm
    exact this ▸ hv

theorem card_Mi {i : ℕ} (hi : i < 2) : Nat.card (Mi i) = 768 := by
  rw [card_of_cols (mem_Mi_iff hi) (mE_spec hi).1 (validN_mE hi)
    (fun x hx => let ⟨u, _, hu⟩ := exists_mem_Mi hi hx; ⟨u, hu⟩), (mE_spec hi).2.1]

theorem PM_le_Mi (i : ℕ) : PM ≤ Mi i :=
  Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem Mi_le_m22 {i : ℕ} (hi : i < 2) : Mi i ≤ m22 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨v, hv, hv'⟩ := Mi_gens_unit hi _ hu
  have hval : ValidN 12 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) := validN_colsN _
  have : u = v := by
    apply Units.ext
    rw [hv', decN_colsN]
  rw [this]
  exact hv

theorem four_le_index_of {M : Subgroup (GL (Fin 12) (ZMod 2))} (m : Fin 4 → ↥M)
    (hm : ∀ i j, (m i : GL (Fin 12) (ZMod 2))⁻¹ * (m j : GL (Fin 12) (ZMod 2)) ∈ PM → i = j) :
    4 ≤ (PM.subgroupOf M).index := by
  have hinj : Function.Injective fun i => (QuotientGroup.mk (m i) : ↥M ⧸ PM.subgroupOf M) := by
    intro i j h
    apply hm
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Subgroup.index] using this

theorem mulVec_eq_of_mem_PM {a b : GL (Fin 12) (ZMod 2)} (h : a⁻¹ * b ∈ PM) :
    (a : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) =
      (b : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) := by
  have h2 := PM_fix h
  rw [Units.val_mul, ← Matrix.mulVec_mulVec] at h2
  calc (a : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0)
      = (a : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (((a⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
            ((b : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0))) := by rw [h2]
    _ = _ := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]

theorem four_le_index {M : Subgroup (GL (Fin 12) (ZMod 2))}
    (m : Fin 4 → ↥M)
    (hm : ∀ i j, ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = ((m j : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) → i = j) :
    4 ≤ (PM.subgroupOf M).index :=
  four_le_index_of m fun i j h => hm i j (mulVec_eq_of_mem_PM h)

theorem mvN_inj_of {q : GL (Fin 12) (ZMod 2)} {c : List ℕ} (hc : ValidN 12 c)
    (hq : (q : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c) {a b : ℕ} (ha : a < 2 ^ 12)
    (hb : b < 2 ^ 12) (h : mvN c a = mvN c b) : a = b := by
  apply vecN_inj ha hb
  have h1 : (q : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 a) =
      (q : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 b) := by
    rw [hq, decN_mulVec hc.1, decN_mulVec hc.1, h]
  have h2 := congrArg (((q⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec)
    h1
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2

theorem eq_Mi_of {M : Subgroup (GL (Fin 12) (ZMod 2))}
    (hMΓ : M ≤ m22) (hPM : PM ≤ M) (hcard : Nat.card M = 768) {y : GL (Fin 12) (ZMod 2)}
    (hyM : y ∈ M)
    (hy : (y : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) ≠ vecN 12 v0) :
    ∃ i < 2, M = Mi i := by
  have hidx : (PM.subgroupOf M).index = 3 := by
    have h := Subgroup.relIndex_mul_card PM M
    rw [inf_eq_left.mpr hPM, card_PM, hcard] at h
    unfold Subgroup.relIndex at h
    omega
  obtain ⟨uw, huw, s, hs, rfl⟩ := decomp (hMΓ hyM)
  have hyv := mulVec_decomp huw hs
  have hu12 := orbL_lt huw
  have hv12 : v0 < 2 ^ 12 := by decide
  have huv0 : uw.1 ≠ v0 := fun h => hy (by rw [hyv, h])
  have hU4 : uw.1 ∈ U4 := by
    rcases ovB_spec.1 uw huw with h | h | ⟨p₁, hp₁, p₂, hp₂, h1, h2, h12⟩
    · exact absurd h huv0
    · exact h
    · exfalso
      obtain ⟨q₁, hq₁, hq₁'⟩ := exists_mem_PM hp₁
      obtain ⟨q₂, hq₂, hq₂'⟩ := exists_mem_PM hp₂
      have hv₁ := (subB_spec pB_spec.1).1 p₁ hp₁
      have hv₂ := (subB_spec pB_spec.1).1 p₂ hp₂
      have hfix₁ : mvN p₁ v0 = v0 := by
        have := PM_fix hq₁
        rw [hq₁', decN_mulVec hv₁.1] at this
        exact vecN_inj (mvN_lt hv₁.2 _) hv12 this
      have hfix₂ : mvN p₂ v0 = v0 := by
        have := PM_fix hq₂
        rw [hq₂', decN_mulVec hv₂.1] at this
        exact vecN_inj (mvN_lt hv₂.2 _) hv12 this
      have hne₁ : mvN p₁ uw.1 ≠ v0 := fun h =>
        huv0 (mvN_inj_of hv₁ hq₁' hu12 hv12 (by rw [h, hfix₁]))
      have hne₂ : mvN p₂ uw.1 ≠ v0 := fun h =>
        huv0 (mvN_inj_of hv₂ hq₂' hu12 hv12 (by rw [h, hfix₂]))
      let m : Fin 4 → ↥M := ![1, ⟨_, hyM⟩, ⟨q₁ * _, M.mul_mem (hPM hq₁) hyM⟩,
        ⟨q₂ * _, M.mul_mem (hPM hq₂) hyM⟩]
      let c : Fin 4 → ℕ := ![v0, uw.1, mvN p₁ uw.1, mvN p₂ uw.1]
      have hc : ∀ i, ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (vecN 12 v0) = vecN 12 (c i) := by
        intro i
        fin_cases i
        · simp [m, c]
        · exact hyv
        · show ((q₁ * _ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec _ = _
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyv, hq₁', decN_mulVec hv₁.1]
          rfl
        · show ((q₂ * _ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec _ = _
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyv, hq₂', decN_mulVec hv₂.1]
          rfl
      have hclt : ∀ i, c i < 2 ^ 12 := by
        intro i
        fin_cases i
        · exact hv12
        · exact hu12
        · exact mvN_lt hv₁.2 _
        · exact mvN_lt hv₂.2 _
      have hcinj : ∀ i j, c i = c j → i = j := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp only [c] at h ⊢ <;> first
          | rfl
          | exact absurd h huv0 | exact absurd h.symm huv0
          | exact absurd h hne₁.symm | exact absurd h.symm hne₁.symm
          | exact absurd h hne₂.symm | exact absurd h.symm hne₂.symm
          | exact absurd h h1.symm | exact absurd h.symm h1.symm
          | exact absurd h h2.symm | exact absurd h.symm h2.symm
          | exact absurd h h12.symm | exact absurd h.symm h12.symm
      have h4 := four_le_index m fun i j h => hcinj i j
        (vecN_inj (hclt i) (hclt j) (by rw [← hc i, ← hc j, h]))
      omega
  obtain ⟨r, hr, hrs⟩ := exists_rP_of_mem_S0 hs
  have hrr := (ovB_spec.2.1 r hr).2
  obtain ⟨hvr1, hvr2⟩ := validN_rP r hr
  obtain ⟨rU, hrU, hrU'⟩ := exists_S0_of_rP hr
  have hinv := inv_val_of hvr1 hvr2 hrU' hrr
  have hpP : rU⁻¹ * s ∈ PM := by
    rw [mem_PM_iff, Units.val_mul, colsN_mul, hinv, colsN_decN hvr2]
    exact hrs
  have hy' : tU uw.2 * rU ∈ M := by
    have : tU uw.2 * rU = (tU uw.2 * s) * (rU⁻¹ * s)⁻¹ := by group
    rw [this]
    exact M.mul_mem hyM (M.inv_mem (hPM hpP))
  have hval' : ValidN 12 (mulN (tW uw.2) r.1) := validN_mulN (validN_evalW gG validN_gG _) hvr1
  have hdec : ((tU uw.2 * rU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      decN 12 (mulN (tW uw.2) r.1) := by
    rw [Units.val_mul, tU_val, hrU', decN_mulN (length_evalW gG _) hvr1.1]
  have hcols : colsN ((tU uw.2 * rU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      mulN (tW uw.2) r.1 := by
    rw [hdec, colsN_decN hval']
  have hgval : ∀ g ∈ pG ++ [mulN (tW uw.2) r.1], ValidN 12 g := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact (subB_spec pB_spec.1).2.2.2.2 g hg
    · rw [List.mem_singleton.mp hg]
      exact hval'
  have hgunit : ∀ g ∈ pG ++ [mulN (tW uw.2) r.1], ∃ u ∈ M,
      (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨u, hu, hu'⟩ := pG_unit g hg
      refine ⟨u, hPM (mem_genSubN_of_mem (subB_spec pB_spec.1).2.2.2.2 hg hu'), hu'⟩
    · rw [List.mem_singleton.mp hg]
      exact ⟨_, hy', hdec⟩
  have hgunit' : ∀ g ∈ pG ++ [mulN (tW uw.2) r.1], ∃ u : GL (Fin 12) (ZMod 2),
      (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
    fun g hg => let ⟨u, _, hu⟩ := hgunit g hg; ⟨u, hu⟩
  have hKM : genSubN 12 (pG ++ [mulN (tW uw.2) r.1]) ≤ M := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    obtain ⟨v, hv, hv'⟩ := hgunit _ hu
    have : u = v := by
      apply Units.ext
      rw [hv', decN_colsN]
    rw [this]
    exact hv
  rcases ovB_spec.2.2.2.1 uw huw hU4 r hr with hin | hfour
  · have key : ∀ i < 2, mulN (tW uw.2) r.1 ∈ mE i → M = Mi i := by
      intro i hi hmem
      have hy'Mi : tU uw.2 * rU ∈ Mi i := (mem_Mi_iff hi _).mpr (hcols ▸ hmem)
      have hPK : PM ≤ genSubN 12 (pG ++ [mulN (tW uw.2) r.1]) :=
        Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu
      have hy'K : tU uw.2 * rU ∈ genSubN 12 (pG ++ [mulN (tW uw.2) r.1]) :=
        Subgroup.subset_closure (show colsN ((tU uw.2 * rU : GL (Fin 12) (ZMod 2)) :
          Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ pG ++ [mulN (tW uw.2) r.1] by
          rw [hcols]
          exact List.mem_append_right _ (List.mem_singleton_self _))
      have hKMi : genSubN 12 (pG ++ [mulN (tW uw.2) r.1]) ≤ Mi i := by
        refine (Subgroup.closure_le _).mpr fun u hu => ?_
        rcases List.mem_append.mp hu with hu | hu
        · exact PM_le_Mi i (Subgroup.subset_closure hu)
        · have : u = tU uw.2 * rU := eq_of_colsN_eq (by rw [List.mem_singleton.mp hu, hcols])
          rw [this]
          exact hy'Mi
      have hy'P : tU uw.2 * rU ∉ PM := fun h => huv0 (vecN_inj hu12 hv12 (by
        rw [← mulVec_decomp huw hrU]
        exact PM_fix h))
      have hK : Nat.card ↥(genSubN 12 (pG ++ [mulN (tW uw.2) r.1])) = 768 := by
        obtain ⟨t, ht⟩ : 256 ∣ Nat.card ↥(genSubN 12 (pG ++ [mulN (tW uw.2) r.1])) :=
          card_PM ▸ Subgroup.card_dvd_of_le hPK
        have h2 : Nat.card ↥(genSubN 12 (pG ++ [mulN (tW uw.2) r.1])) ∣ 768 :=
          hcard ▸ Subgroup.card_dvd_of_le hKM
        have h3 : t ≠ 1 := by
          rintro rfl
          apply hy'P
          have : genSubN 12 (pG ++ [mulN (tW uw.2) r.1]) = PM :=
            (Subgroup.eq_of_le_of_card_ge hPK (by rw [ht, card_PM])).symm
          exact this ▸ hy'K
        rw [ht] at h2 ⊢
        have h4 : t ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 256) (by simpa using h2)
        rcases (Nat.dvd_prime (by norm_num)).mp h4 with h5 | h5
        · exact absurd h5 h3
        · rw [h5]
      have hMK : genSubN 12 (pG ++ [mulN (tW uw.2) r.1]) = M :=
        Subgroup.eq_of_le_of_card_ge hKM (by rw [hcard, hK])
      exact Subgroup.eq_of_le_of_card_ge (hMK ▸ hKMi) (by rw [card_Mi hi, hcard])
    rcases hin with h | h
    · exact ⟨0, by norm_num, key 0 (by norm_num) h⟩
    · exact ⟨1, by norm_num, key 1 (by norm_num) h⟩
  ·
    exfalso
    simp only [ovFourB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, Bool.or_eq_true,
      beq_iff_eq, Bool.not_eq_true', Std.HashSet.contains_ofList] at hfour
    obtain ⟨⟨⟨hy0, ha0⟩, hay⟩, w, -, hz⟩ := hfour
    obtain ⟨ua, hua, hua'⟩ := exists_evalW _ hgval hgunit' [0, 5]
    obtain ⟨uz, huz, huz'⟩ := exists_evalW _ hgval hgunit' w
    have hva := validN_evalW _ hgval [0, 5]
    have hvz := validN_evalW _ hgval w
    have img : ∀ {u : GL (Fin 12) (ZMod 2)} {c : List ℕ}, ValidN 12 c →
        (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c →
        (u : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 (mvN c v0) := by
      intro u c hc hu
      rw [hu, decN_mulVec hc.1]
    let m : Fin 4 → ↥M := ![1, ⟨_, hy'⟩, ⟨ua, hKM hua⟩, ⟨uz, hKM huz⟩]
    let c : Fin 4 → ℕ := ![v0, mvN (mulN (tW uw.2) r.1) v0,
      mvN (evalW 12 (pG ++ [mulN (tW uw.2) r.1]) [0, 5]) v0,
      mvN (evalW 12 (pG ++ [mulN (tW uw.2) r.1]) w) v0]
    have hc : ∀ i, ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (vecN 12 v0) = vecN 12 (c i) := by
      intro i
      fin_cases i
      · simp [m, c]
      · exact img hval' hdec
      · exact img hva hua'
      · exact img hvz huz'
    have hclt : ∀ i, c i < 2 ^ 12 := by
      intro i
      fin_cases i
      · exact hv12
      · exact mvN_lt hval'.2 _
      · exact mvN_lt hva.2 _
      · exact mvN_lt hvz.2 _
    have hceq : ∀ i j, (m i : GL (Fin 12) (ZMod 2))⁻¹ * (m j : GL (Fin 12) (ZMod 2)) ∈ PM →
        c i = c j := fun i j h =>
      vecN_inj (hclt i) (hclt j) (by rw [← hc i, ← hc j]; exact mulVec_eq_of_mem_PM h)
    have hzP : uz ∈ PM → evalW 12 (pG ++ [mulN (tW uw.2) r.1]) w ∈ pE := fun h => by
      rw [← colsN_decN hvz, ← huz']
      exact (mem_PM_iff uz).mp h
    have h4 := four_le_index_of m fun i j h => by
      have hij := hceq i j h
      rcases hz with ⟨⟨hz1, hz2⟩, hz3⟩ | ⟨hz1, hz2⟩
      · fin_cases i <;> fin_cases j <;> simp [c] at hij ⊢ <;> omega
      · have hz2' : evalW 12 (pG ++ [mulN (tW uw.2) r.1]) w ∉ pE := by simpa using hz2
        fin_cases i <;> fin_cases j <;> simp [c] at hij ⊢ <;>
          first
          | omega
          | exact hz2' (hzP (by simpa [m] using h))
    omega

end CFSG.Quasithin.H13.M22Cert
