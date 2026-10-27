module

public import CFSG.Quasithin.H13.L32NM22Model

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert L1442M

theorem unit_of_s0E {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ s0E) :
    ∀ g ∈ gens, ∃ u : GL (Fin 12) (ZMod 2), (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_S0 (h g hg); ⟨u, hu⟩

theorem genSubN_le_S0 {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ s0E) : genSubN 12 gens ≤ S0 :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_S0_iff u).mpr (h _ hu)

theorem inv_val_of {u : GL (Fin 12) (ZMod 2)} {c c' : List ℕ} (hc : ValidN 12 c)
    (hc' : ValidN 12 c') (hu : (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c)
    (h : mulN c c' = one12) : ((u⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      decN 12 c' := by
  have h1 : (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) * decN 12 c' = 1 := by
    rw [hu, ← decN_mulN hc.1 hc'.1, h, decN_oneN]
  calc ((u⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
      = ((u⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
          ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)) * decN 12 c') := by rw [h1, Matrix.mul_one]
    _ = decN 12 c' := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]

@[expose] def PM : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 pG

theorem pB_spec :
    subB 12 pG pE = true ∧ pE.length = 256 ∧ (∀ g ∈ pG, g ∈ s0E) ∧
      ∀ v < 4096, (∀ g ∈ pG, mvN g v = v) → v = 0 ∨ v = v0 := by
  have h := m22Check_parts.2.2.2.2.1
  simp only [pB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun v hv hfix => ?_⟩
  have := h4 v (List.mem_range.mpr hv)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  rcases this with (h5 | h5) | h5
  · exfalso
    have h6 : (pG.all fun p => mvN p v == v) = true := by
      simp only [List.all_eq_true, beq_iff_eq]
      exact hfix
    rw [h6] at h5
    exact Bool.noConfusion h5
  · exact Or.inl h5
  · exact Or.inr h5

theorem PM_le_S0 : PM ≤ S0 := genSubN_le_S0 pB_spec.2.2.1

theorem PM_le_m22 : PM ≤ m22 := PM_le_S0.trans S0_le

theorem mem_PM_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ PM ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ pE :=
  mem_genSubN_iff_of pB_spec.1 (unit_of_s0E pB_spec.2.2.1) u

theorem card_PM : Nat.card PM = 256 := by
  rw [PM, card_genSubN_of pB_spec.1 (unit_of_s0E pB_spec.2.2.1)]
  exact pB_spec.2.1

theorem exists_mem_PM {c : List ℕ} (hc : c ∈ pE) :
    ∃ u ∈ PM, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c :=
  exists_mem_of_elemsOf pB_spec.1 (unit_of_s0E pB_spec.2.2.1) hc

theorem PM_fix {p : GL (Fin 12) (ZMod 2)} (hp : p ∈ PM) :
    (p : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0 :=
  S0_fix (PM_le_S0 hp)

theorem eq_of_fixed_PM (v : Fin 12 → ZMod 2)
    (hv : ∀ γ ∈ PM, (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = vecN 12 v0 := by
  have hval := (subB_spec pB_spec.1).2.2.2.2
  have hfix : ∀ p ∈ pG, mvN p (codeN v) = codeN v := by
    intro p hp
    obtain ⟨u, hu⟩ := unit_of_s0E pB_spec.2.2.1 p hp
    have := hv u (mem_genSubN_of_mem hval hp hu)
    rw [← vecN_codeN v, hu, decN_mulVec (hval p hp).1] at this
    exact vecN_inj (mvN_lt (hval p hp).2 _) (codeN_lt v) (by rw [this, vecN_codeN])
  rcases pB_spec.2.2.2 (codeN v) (codeN_lt v) hfix with h | h
  · left
    rw [← vecN_codeN v, h, vecN_zero]
  · right
    rw [← vecN_codeN v, h]

@[expose] def E0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 e0G

theorem e0B_spec :
    subB 12 e0G e0E = true ∧ e0E.length = 32 ∧ (∀ g ∈ e0G, g ∈ pE) ∧
      (∀ c ∈ cjL, c.1 ∈ s0E ∧ mulN c.1 c.2 = one12) ∧
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

theorem mem_s0E_of_pE {c : List ℕ} (hc : c ∈ pE) : c ∈ s0E := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_PM hc
  rw [← colsN_decN ((subB_spec pB_spec.1).1 c hc), ← hu']
  exact (mem_S0_iff u).mp (PM_le_S0 hu)

theorem e0G_mem : ∀ g ∈ e0G, g ∈ s0E :=
  fun g hg => mem_s0E_of_pE (e0B_spec.2.2.1 g hg)

theorem mem_E0_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ E0 ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ e0E :=
  mem_genSubN_iff_of e0B_spec.1 (unit_of_s0E e0G_mem) u

theorem card_E0 : Nat.card E0 = 32 := by
  rw [E0, card_genSubN_of e0B_spec.1 (unit_of_s0E e0G_mem)]
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

theorem le_E0_of {W : Subgroup (GL (Fin 12) (ZMod 2))}
    (hWP : W ≤ PM) (hnorm : ∀ ν ∈ S0, ∀ x ∈ W, ν * x * ν⁻¹ ∈ W) : W ≤ E0 := by
  intro x hx
  rw [mem_E0_iff]
  have hxP := (mem_PM_iff x).mp (hWP hx)
  rcases e0B_spec.2.2.2.2 _ hxP with h | ⟨c, hc, hout⟩
  · exact h
  · exfalso
    obtain ⟨hc1, hcc⟩ := e0B_spec.2.2.2.1 c hc
    obtain ⟨hv1, hv2⟩ := validN_cjL c hc
    obtain ⟨u, hu, hu'⟩ := exists_mem_S0 hc1
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
    (∀ r ∈ rP, r.1 ∈ s0E ∧ mulN r.1 r.2 = one12) ∧
    (∀ s ∈ s0E, ∃ r ∈ rP, mulN r.2 s ∈ pE) ∧
    (∀ uw ∈ orbL, uw.1 ∈ U4 → ∀ r ∈ rP,
      (mulN (tW uw.2) r.1 ∈ mE 0 ∨ mulN (tW uw.2) r.1 ∈ mE 1) ∨
        (769 ≤ (elemsOf 12 (pG ++ [mulN (tW uw.2) r.1]) 769).length ∧
          nodupB 12 (elemsOf 12 (pG ++ [mulN (tW uw.2) r.1]) 769) = true)) ∧
    ∀ i ∈ [0, 1], subB 12 (pG ++ [mRep.getD i one12]) (mE i) = true ∧ (mE i).length = 768 := by
  have h := m22Check_parts.2.2.2.2.2.2.2.1
  simp only [ovB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun uw huw => ?_, fun r hr => ?_, fun s hs => ?_, fun uw huw hU r hr => ?_,
    fun i hi => ?_⟩
  · have := h1 uw huw
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, List.any_eq_true,
      Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with (h | h) | ⟨p₁, hp₁, h6, p₂, hp₂, h7, h8⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨p₁, hp₁, p₂, hp₂, h6, h7, h8⟩)
  · have := h2 r hr
    simp only [beq_iff_eq, Std.HashSet.contains_ofList, List.contains_iff_mem] at this
    exact this
  · have := h3 s hs
    simp only [List.any_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem] at this
    exact this
  · have := h4 uw huw
    have hc : U4.contains uw.1 = true := List.contains_iff_mem.mpr hU
    simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    have := this r hr
    simp only [Bool.or_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem,
      Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have := h5 i hi
    simp only [beq_iff_eq] at this
    exact this

theorem validN_rP : ∀ r ∈ rP, ValidN 12 r.1 ∧ ValidN 12 r.2 := by
  have h : ∀ r ∈ rP, validB 12 r.1 = true ∧ validB 12 r.2 = true := by decide
  intro r hr
  exact ⟨validB_iff.mp (h r hr).1, validB_iff.mp (h r hr).2⟩

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
    obtain ⟨rU, hrU, hrU'⟩ := exists_mem_S0 (ovB_spec.2.1 r hr).1
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
  · obtain ⟨u, hu, hu'⟩ := exists_mem_S0 (pB_spec.2.2.1 g hg)
    exact ⟨u, S0_le hu, hu'⟩
  · rw [List.mem_singleton.mp hg]
    exact mRep_unit hi

theorem mE_spec {i : ℕ} (hi : i < 2) :
    subB 12 (pG ++ [mRep.getD i one12]) (mE i) = true ∧ (mE i).length = 768 :=
  ovB_spec.2.2.2.2 i (by interval_cases i <;> simp)

theorem mem_Mi_iff {i : ℕ} (hi : i < 2) (u : GL (Fin 12) (ZMod 2)) :
    u ∈ Mi i ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ mE i :=
  mem_genSubN_iff_of (mE_spec hi).1 (fun g hg => let ⟨u, _, hu⟩ := Mi_gens_unit hi g hg; ⟨u, hu⟩) u

theorem card_Mi {i : ℕ} (hi : i < 2) : Nat.card (Mi i) = 768 := by
  rw [Mi, card_genSubN_of (mE_spec hi).1
    (fun g hg => let ⟨u, _, hu⟩ := Mi_gens_unit hi g hg; ⟨u, hu⟩)]
  exact (mE_spec hi).2

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

theorem four_le_index {M : Subgroup (GL (Fin 12) (ZMod 2))}
    (m : Fin 4 → ↥M)
    (hm : ∀ i j, ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = ((m j : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) → i = j) :
    4 ≤ (PM.subgroupOf M).index := by
  have hinj : Function.Injective fun i => (QuotientGroup.mk (m i) : ↥M ⧸ PM.subgroupOf M) := by
    intro i j h
    apply hm
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
    have h2 := PM_fix h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at h2
    rw [← Matrix.mulVec_mulVec] at h2
    calc ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0)
        = ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
            ((((m i)⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
              (((m j : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
                (vecN 12 v0))) := by rw [h2]
      _ = _ := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Subgroup.index] using this

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
  obtain ⟨r, hr, hrs⟩ := ovB_spec.2.2.1 _ ((mem_S0_iff s).mp hs)
  obtain ⟨hr1, hrr⟩ := ovB_spec.2.1 r hr
  obtain ⟨hvr1, hvr2⟩ := validN_rP r hr
  obtain ⟨rU, hrU, hrU'⟩ := exists_mem_S0 hr1
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
    · obtain ⟨u, hu, hu'⟩ := exists_mem_S0 (pB_spec.2.2.1 g hg)
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
  rcases ovB_spec.2.2.2.1 uw huw hU4 r hr with hin | ⟨hbig, hnd⟩
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
  · exfalso
    have hB : ∀ b ∈ elemsOf 12 (pG ++ [mulN (tW uw.2) r.1]) 769, ∃ u ∈ M,
        (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 b := by
      intro b hb
      obtain ⟨w, rfl⟩ := mem_elemsOf hb
      obtain ⟨u, hu, hu'⟩ := exists_evalW _ hgval hgunit' w
      exact ⟨u, hKM hu, hu'⟩
    have hval : ∀ b ∈ elemsOf 12 (pG ++ [mulN (tW uw.2) r.1]) 769, ValidN 12 b := by
      intro b hb
      obtain ⟨w, rfl⟩ := mem_elemsOf hb
      exact validN_evalW _ hgval w
    have := le_card_of_list (nodup_of_nodupB hnd) hB hval
    omega

end CFSG.Quasithin.H13.M22Cert
