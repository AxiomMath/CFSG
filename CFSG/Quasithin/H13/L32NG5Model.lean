module

public import CFSG.Quasithin.H13.L32NS8Model2
public import Certificates.Certificate7188

public section

namespace CFSG.Quasithin.H13.G5Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert

theorem g5Check_eq : g5Check = true :=
  Certificates.certificate7188

theorem g5Check_parts :
    basicB = true ∧ pB = true ∧ zB = true ∧ wB = true ∧ ovB = true ∧ oB = true ∧
      m12B = true := by
  have h := g5Check_eq
  simp only [g5Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

@[expose] def b5V (v w : Fin 8 → ZMod 2) : ZMod 2 :=
  quadOf q5n (v + w) + quadOf q5n v + quadOf q5n w

theorem q5c_eq : dec8 q5c = q5n := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem quadN_spec (v : ℕ) : b2z (quadN v) = quadOf q5n (vec8 v) := by
  rw [quadN, dotN_spec, ← dec8_mulVec, q5c_eq]
  rfl

theorem b5N_spec (v w : ℕ) : b2z (b5N v w) = b5V (vec8 v) (vec8 w) := by
  simp only [b5N, b2z_xor, quadN_spec, vec8_xor, b5V]

theorem gSG_cols : gSG = [colsOf (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5n0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5n1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5n2 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5nf : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem gAG_cols : gAG = [colsOf (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5n0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5n1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5n2 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem gSG_unit : ∀ c ∈ gSG, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  rw [gSG_cols]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g5s0, (dec8_colsOf _).symm⟩
  · exact ⟨g5s1, (dec8_colsOf _).symm⟩
  · exact ⟨g5n0, (dec8_colsOf _).symm⟩
  · exact ⟨g5n1, (dec8_colsOf _).symm⟩
  · exact ⟨g5n2, (dec8_colsOf _).symm⟩
  · exact ⟨g5nf, (dec8_colsOf _).symm⟩

theorem gAG_unit : ∀ c ∈ gAG, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := fun c hc =>
  gSG_unit c (List.mem_of_mem_take hc)

theorem gS_eq : g5 true true = genSub gSG := by
  show Subgroup.closure _ = genSub gSG
  unfold genSub
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, gSG_cols,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h)))))

theorem gA_eq : g5 false true = genSub gAG := by
  show Subgroup.closure _ = genSub gAG
  unfold genSub
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, gAG_cols,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
  · rintro (h | h | h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_colsOf_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (eq_of_colsOf_eq h))))

theorem basic_spec :
    subB gSG gSE = true ∧ gSE.length = 720 ∧ subB gAG gAE = true ∧ gAE.length = 360 := by
  have h := g5Check_parts.1
  simp only [basicB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem mem_gS_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ g5 true true ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gSE := by
  rw [gS_eq]
  exact mem_genSub_iff_of basic_spec.1 gSG_unit u

theorem mem_gA_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ g5 false true ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gAE := by
  rw [gA_eq]
  exact mem_genSub_iff_of basic_spec.2.2.1 gAG_unit u

theorem card_gS : Nat.card (g5 true true) = 720 := by
  rw [gS_eq, card_genSub_of basic_spec.1 gSG_unit]
  exact basic_spec.2.1

theorem card_gA : Nat.card (g5 false true) = 360 := by
  rw [gA_eq, card_genSub_of basic_spec.2.2.1 gAG_unit]
  exact basic_spec.2.2.2

theorem exists_mem_gS {c : List ℕ} (hc : c ∈ gSE) :
    ∃ u ∈ g5 true true, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  rw [gS_eq]
  exact exists_evalW gSG (subB_spec basic_spec.1).2.2.2.2 gSG_unit w

theorem exists_mem_gA {c : List ℕ} (hc : c ∈ gAE) :
    ∃ u ∈ g5 false true, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  rw [gA_eq]
  exact exists_evalW gAG (subB_spec basic_spec.2.2.1).2.2.2.2 gAG_unit w

theorem genSub_le_gS {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ gSE) : genSub gens ≤ g5 true true :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_gS_iff u).mpr (hgens _ hu)

theorem genSub_le_gA {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ gAE) : genSub gens ≤ g5 false true :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_gA_iff u).mpr (hgens _ hu)

theorem unit_of_gSE {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ gSE) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_gS (hgens g hg); ⟨u, hu⟩

theorem unit_of_gAE {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ gAE) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_gA (hgens g hg); ⟨u, hu⟩

@[expose] def PS : Subgroup (GL (Fin 8) (ZMod 2)) := genSub pSG

@[expose] def PA : Subgroup (GL (Fin 8) (ZMod 2)) := genSub pAG

theorem pB_spec :
    (elemsOf pSG).length = 16 ∧ subB pSG (elemsOf pSG) = true ∧ (∀ g ∈ pSG, g ∈ gSE) ∧
      (elemsOf pAG).length = 8 ∧ subB pAG (elemsOf pAG) = true ∧ (∀ g ∈ pAG, g ∈ gAE) ∧
      (∀ v < 256, (∀ p ∈ pSG, mv8 p v = v) → v = 0 ∨ v = vS) ∧
      (∀ v < 256, (∀ p ∈ pAG, mv8 p v = v) → v < 4) ∧
      (∀ y ∈ gSE, mv8 y vS = vS → y ∈ elemsOf pSG) ∧
      ∀ y ∈ gAE, ∀ v ∈ [1, 2, 3], mv8 y v = v → y ∈ elemsOf pAG := by
  have h := g5Check_parts.2.1
  simp only [pB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun v hv hfix => ?_, fun v hv hfix => ?_,
    fun y hy hyf => ?_, fun y hy v hv hvf => ?_⟩
  · rcases h7 v (List.mem_range.mpr hv) with (h | h) | h
    · exfalso
      have : (pSG.all fun p => mv8 p v == v) = true := by
        simp only [List.all_eq_true, beq_iff_eq]; exact hfix
      rw [this] at h
      exact Bool.noConfusion h
    · exact Or.inl h
    · exact Or.inr h
  · rcases h8 v (List.mem_range.mpr hv) with h | h
    · exfalso
      have : (pAG.all fun p => mv8 p v == v) = true := by
        simp only [List.all_eq_true, beq_iff_eq]; exact hfix
      rw [this] at h
      exact Bool.noConfusion h
    · exact h
  · rcases h9 y hy with h | h
    · exact absurd hyf (by simpa using h)
    · exact h
  · rcases h10 y hy v hv with h | h
    · exact absurd hvf (by simpa using h)
    · exact h

theorem PS_le_gS : PS ≤ g5 true true := genSub_le_gS pB_spec.2.2.1

theorem PA_le_gA : PA ≤ g5 false true :=
  genSub_le_gA pB_spec.2.2.2.2.2.1

theorem mem_PS_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ PS ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf pSG :=
  mem_genSub_iff_of pB_spec.2.1 (unit_of_gSE pB_spec.2.2.1) u

theorem mem_PA_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ PA ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf pAG :=
  mem_genSub_iff_of pB_spec.2.2.2.2.1 (unit_of_gAE pB_spec.2.2.2.2.2.1) u

theorem card_PS : Nat.card PS = 16 := by
  rw [PS, card_genSub_of pB_spec.2.1 (unit_of_gSE pB_spec.2.2.1), pB_spec.1]

theorem card_PA : Nat.card PA = 8 := by
  rw [PA, card_genSub_of pB_spec.2.2.2.2.1 (unit_of_gAE pB_spec.2.2.2.2.2.1),
    pB_spec.2.2.2.1]

theorem fixed_code {gens : List (List ℕ)} (hgens : ∀ g ∈ gens, Valid8 g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    {v : Fin 8 → ZMod 2}
    (hv : ∀ g ∈ genSub gens, (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    ∀ p ∈ gens, mv8 p (code8 v) = code8 v := by
  intro p hp
  obtain ⟨u, hu⟩ := hunit p hp
  have := hv u (mem_genSub_of_mem hgens hp hu)
  rw [← vec8_code8 v, hu, dec8_mulVec] at this
  exact vec8_inj (mv8_lt (hgens p hp) _) (code8_lt v) (by rw [this, vec8_code8])

theorem eq_of_fixed_PS (v : Fin 8 → ZMod 2)
    (hv : ∀ g ∈ PS, (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = vec8 vS := by
  rcases pB_spec.2.2.2.2.2.2.1 (code8 v) (code8_lt v)
      (fixed_code (subB_spec pB_spec.2.1).2.2.2.2 (unit_of_gSE pB_spec.2.2.1) hv) with h | h
  · exact Or.inl (by rw [← vec8_code8 v, h, vec8_zero])
  · exact Or.inr (by rw [← vec8_code8 v, h])

theorem code_lt_of_fixed_PA (v : Fin 8 → ZMod 2)
    (hv : ∀ g ∈ PA, (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) : code8 v < 4 :=
  pB_spec.2.2.2.2.2.2.2.1 (code8 v) (code8_lt v)
    (fixed_code (subB_spec pB_spec.2.2.2.2.1).2.2.2.2 (unit_of_gAE pB_spec.2.2.2.2.2.1) hv)

theorem mem_PS_of_fix {y : GL (Fin 8) (ZMod 2)}
    (hy : y ∈ g5 true true)
    (hfix : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vS) = vec8 vS) : y ∈ PS := by
  rw [mem_PS_iff]
  refine pB_spec.2.2.2.2.2.2.2.2.1 _ ((mem_gS_iff y).mp hy) ?_
  rw [mulVec_vec8] at hfix
  exact vec8_inj (mv8_lt (valid8_colsOf _) _) (by decide) hfix

theorem mem_PA_of_fix {y : GL (Fin 8) (ZMod 2)}
    (hy : y ∈ g5 false true) {v : ℕ} (hv : v ∈ [1, 2, 3])
    (hfix : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 v) = vec8 v) : y ∈ PA := by
  rw [mem_PA_iff]
  refine pB_spec.2.2.2.2.2.2.2.2.2 _ ((mem_gA_iff y).mp hy) v hv ?_
  have hv4 : v < 256 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; omega
  rw [mulVec_vec8] at hfix
  exact vec8_inj (mv8_lt (valid8_colsOf _) _) hv4 hfix

theorem zB_spec :
    (∀ z ∈ zPG, z ∈ elemsOf pSG ∧ ∀ p ∈ pSG, mul8 z p = mul8 p z) ∧
      mul8 (pSG.getD 2 one8) (pSG.getD 3 one8) ≠ mul8 (pSG.getD 3 one8) (pSG.getD 2 one8) := by
  have h := g5Check_parts.2.2.1
  simp only [zB, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact h

theorem zPS_central {z : GL (Fin 8) (ZMod 2)}
    (hz : colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zPG) {p : GL (Fin 8) (ZMod 2)}
    (hp : p ∈ PS) : z * p = p * z := by
  have hzc := (zB_spec.1 _ hz).2
  have hle : PS ≤ Subgroup.centralizer {z} := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    apply eq_of_colsOf_eq
    rw [Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul]
    exact hzc _ hu
  exact Subgroup.mem_centralizer_iff.mp (hle hp) z rfl

theorem not_comm_PS :
    ∃ p ∈ PS, ∃ p' ∈ PS, p * p' ≠ p' * p := by
  have hval := (subB_spec pB_spec.2.1).2.2.2.2
  have h2 : pSG.getD 2 one8 ∈ pSG := by simp [pSG]
  have h3 : pSG.getD 3 one8 ∈ pSG := by simp [pSG]
  obtain ⟨u, hu⟩ := unit_of_gSE pB_spec.2.2.1 _ h2
  obtain ⟨u', hu'⟩ := unit_of_gSE pB_spec.2.2.1 _ h3
  refine ⟨u, mem_genSub_of_mem hval h2 hu, u', mem_genSub_of_mem hval h3 hu', fun h => ?_⟩
  apply zB_spec.2
  have := congrArg (fun y : GL (Fin 8) (ZMod 2) => colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) h
  simp only [Units.val_mul, colsOf_mul, hu, hu', colsOf_dec8 (hval _ h2),
    colsOf_dec8 (hval _ h3)] at this
  exact this

theorem wB_spec :
    (∀ p ∈ eWS, p.1 ∈ zPG ∧ b5N p.2 vS = false) ∧
      ∀ v ∈ [1, 2, 3], (∀ p ∈ eWA v, p.1 ∈ elemsOf pAG ∧ b5N p.2 v = false) ∧
        (eSpanA v).length = 32 ∧ (eSpanA v).Nodup := by
  have h := g5Check_parts.2.2.2.1
  simp only [wB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun v hv => ?_⟩
  obtain ⟨⟨h3, h4⟩, h5⟩ := h2 v hv
  refine ⟨h3, h4, ?_⟩
  simp only [nodupN, decide_eq_true_eq] at h5
  have h6 : ((eSpanA v).mergeSort).Nodup :=
    (List.isChain_iff_pairwise.mp h5).imp (fun hab => ne_of_lt hab)
  exact (List.mergeSort_perm _ _).nodup_iff.mp h6

theorem eSpanA_lt : ∀ v ∈ [1, 2, 3], ∀ c ∈ eSpanA v, c < 256 := by decide

theorem card_le_of_eSpanA {v : ℕ} (hv : v ∈ [1, 2, 3])
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ p ∈ eWA v, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) : 32 ≤ Nat.card W := by
  classical
  have hmem : ∀ c ∈ eSpanA v, vec8 c ∈ W := by
    refine spanN_mem _ W ?_
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact hW p hp
  let f : {c // c ∈ eSpanA v} → W := fun c => ⟨vec8 c.1, hmem c.1 c.2⟩
  have hf : Function.Injective f := fun c c' h => Subtype.ext (vec8_inj (eSpanA_lt v hv _ c.2)
    (eSpanA_lt v hv _ c'.2) (congrArg Subtype.val h))
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (List.mem_toFinset (l := eSpanA v) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (wB_spec.2 v hv).2.2, (wB_spec.2 v hv).2.1] at h

theorem eSpanS_mem (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ p ∈ eWS, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) : ∀ c ∈ eSpanS, vec8 c ∈ W := by
  refine spanN_mem _ W ?_
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact hW p hp

end CFSG.Quasithin.H13.G5Cert
