module

public import CFSG.Quasithin.H13.L32NM22Model2
public import CFSG.Quasithin.H13.L32NS7Model3

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert L1442M CFSG.Quasithin

@[expose] def OS (i : ℕ) : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 (oddOf (mE i))

theorem oB_spec :
    ∀ i ∈ [0, 1], subB 12 (oddOf (mE i)) (oE i) = true ∧ (twoOf (oE i)).Nodup ∧
      (oE i).length = 3 * (twoOf (oE i)).length ∧
      (∀ a ∈ twoOf (oE i), ∀ b ∈ twoOf (oE i), mulN a b ∈ twoOf (oE i)) ∧
      (∀ o ∈ oE i, sqN o 8 = one12 → sqN o 2 = one12) ∧
      (∀ y ∈ oE i, mvN y v0 ^^^ v0 ∈ [0, (oWs.getD i (0, 0)).1, (oWs.getD i (0, 0)).2,
        (oWs.getD i (0, 0)).1 ^^^ (oWs.getD i (0, 0)).2]) ∧
      (∃ y ∈ oE i, mvN y v0 ^^^ v0 = (oWs.getD i (0, 0)).1) ∧
      (∃ y ∈ oE i, mvN y v0 ^^^ v0 = (oWs.getD i (0, 0)).2) ∧
      ∃ y ∈ oE i, ∃ v ∈ List.range 4096,
        polN 12 q12c (mvN y v ^^^ v) (oWs.getD i (0, 0)).1 = true := by
  have h := m22Check_parts.2.2.2.2.2.2.2.2.1
  simp only [oB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  intro i hi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩ := h i hi
  refine ⟨a, nodup_of_nodupB b, c, fun x hx y hy => ?_, fun o ho h8 => ?_, fun y hy => ?_, ?_, ?_,
    ?_⟩
  · simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using d x hx y hy
  · have := e o ho
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at this
    exact this.resolve_left (not_not.mpr h8)
  · simpa [List.contains_iff_mem] using f y hy
  · simpa [List.any_eq_true] using g
  · simpa [List.any_eq_true] using k
  · simpa [List.any_eq_true] using l

theorem mem_zero_one {i : ℕ} (hi : i < 2) : i ∈ [0, 1] := by
  interval_cases i <;> simp

theorem oddOf_sub {M : List (List ℕ)} : ∀ x ∈ oddOf M, x ∈ M := fun _ hx =>
  (List.mem_filter.mp hx).1

theorem OS_gens_unit {i : ℕ} (hi : i < 2) :
    ∀ g ∈ oddOf (mE i), ∃ u ∈ Mi i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  exact exists_mem_of_elemsOf (mE_spec hi).1
    (fun g hg => let ⟨u, _, hu⟩ := Mi_gens_unit hi g hg; ⟨u, hu⟩) (oddOf_sub g hg)

theorem OS_le_Mi {i : ℕ} (hi : i < 2) : OS i ≤ Mi i := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  exact (mem_Mi_iff hi u).mpr (oddOf_sub _ hu)

theorem mem_OS_iff {i : ℕ} (hi : i < 2) (u : GL (Fin 12) (ZMod 2)) :
    u ∈ OS i ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ oE i :=
  mem_genSubN_iff_of (oB_spec i (mem_zero_one hi)).1
    (fun g hg => let ⟨u, _, hu⟩ := OS_gens_unit hi g hg; ⟨u, hu⟩) u

theorem exists_OS_of {i : ℕ} (hi : i < 2) {c : List ℕ}
    (hc : c ∈ oE i) : ∃ u ∈ OS i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c :=
  exists_mem_of_elemsOf (oB_spec i (mem_zero_one hi)).1
    (fun g hg => let ⟨u, _, hu⟩ := OS_gens_unit hi g hg; ⟨u, hu⟩) hc

theorem oTwoUpper_Mi {i : ℕ} (hi : i < 2) :
    oTwoUpper (Mi i) = OS i := by
  have hcard : Nat.card (Mi i) = 2 ^ 8 * 3 := (card_Mi hi).trans (by norm_num)
  unfold oTwoUpper OS genSubN
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine List.mem_filter.mpr ⟨(mem_Mi_iff hi u).mp h1, ?_⟩
    rw [beq_iff_eq, ← colsN_pow, (odd_orderOf_iff_of_card hcard h1).mp h2, Units.val_one,
      colsN_one]
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    have hu : u ∈ Mi i := (mem_Mi_iff hi u).mpr h1
    refine ⟨hu, (odd_orderOf_iff_of_card hcard hu).mpr ?_⟩
    rw [beq_iff_eq, ← colsN_pow] at h2
    exact (eq_one_iff_colsN _).mpr h2

theorem OS_vec {i : ℕ} (hi : i < 2) {y : GL (Fin 12) (ZMod 2)}
    (hy : y ∈ OS i) :
    (y : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) + vecN 12 v0 ∈
      ({0, vecN 12 (oWs.getD i (0, 0)).1, vecN 12 (oWs.getD i (0, 0)).2,
        vecN 12 (oWs.getD i (0, 0)).1 + vecN 12 (oWs.getD i (0, 0)).2} :
          Set (Fin 12 → ZMod 2)) := by
  have hmem := (oB_spec i (mem_zero_one hi)).2.2.2.2.2.1 _ ((mem_OS_iff hi y).mp hy)
  rw [mulVec_vecN, ← vecN_xor (mvN _ v0) v0]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> rw [h]
  · exact Or.inl vecN_zero
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (vecN_xor _ _)))

theorem OS_vec_eq {i : ℕ} (hi : i < 2) :
    (∃ y ∈ OS i, (y : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) + vecN 12 v0 =
      vecN 12 (oWs.getD i (0, 0)).1) ∧
    ∃ y ∈ OS i, (y : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) + vecN 12 v0 =
      vecN 12 (oWs.getD i (0, 0)).2 := by
  have h := oB_spec i (mem_zero_one hi)
  have hval := (subB_spec h.1).1
  constructor
  · obtain ⟨c, hc, hcw⟩ := h.2.2.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := exists_OS_of hi hc
    exact ⟨u, hu, by rw [hu', decN_mulVec (hval c hc).1, ← vecN_xor, hcw]⟩
  · obtain ⟨c, hc, hcw⟩ := h.2.2.2.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := exists_OS_of hi hc
    exact ⟨u, hu, by rw [hu', decN_mulVec (hval c hc).1, ← vecN_xor, hcw]⟩

theorem oWs_ne {i : ℕ} (hi : i < 2) :
    vecN 12 (oWs.getD i (0, 0)).1 ≠ 0 ∧ vecN 12 (oWs.getD i (0, 0)).2 ≠ 0 ∧
      vecN 12 (oWs.getD i (0, 0)).1 ≠ vecN 12 (oWs.getD i (0, 0)).2 := by
  interval_cases i <;> decide

theorem OS_pol {i : ℕ} (hi : i < 2) :
    ∃ y ∈ OS i, ∃ v : ℕ, polV q12 ((y : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v) +
      vecN 12 v) (vecN 12 (oWs.getD i (0, 0)).1) = 1 := by
  have h := oB_spec i (mem_zero_one hi)
  obtain ⟨c, hc, v, -, hv⟩ := h.2.2.2.2.2.2.2.2
  obtain ⟨u, hu, hu'⟩ := exists_OS_of hi hc
  refine ⟨u, hu, v, ?_⟩
  rw [hu', decN_mulVec ((subB_spec h.1).1 c hc).1, ← vecN_xor, ← polN_q12, hv]
  rfl

theorem OS_ne : OS 0 ≠ OS 1 := by
  intro h
  obtain ⟨y, hy, hyw⟩ := (OS_vec_eq (i := 0) (by norm_num)).1
  have := OS_vec (i := 1) (by norm_num) (h ▸ hy)
  rw [hyw] at this
  revert this
  decide

@[expose] def RS (i : ℕ) (hi : i < 2) :
    Subgroup (GL (Fin 12) (ZMod 2)) where
  carrier := {u | colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ twoOf (oE i)}
  one_mem' := by
    show colsN ((1 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ twoOf (oE i)
    rw [Units.val_one, colsN_one]
    exact List.mem_filter.mpr ⟨(subB_spec (oB_spec i (mem_zero_one hi)).1).2.2.2.1, by decide⟩
  mul_mem' := fun {a b} ha hb => by
    show colsN ((a * b : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈
      twoOf (oE i)
    rw [Units.val_mul, colsN_mul]
    exact (oB_spec i (mem_zero_one hi)).2.2.2.1 _ ha _ hb
  inv_mem' := fun {a} ha => by
    show colsN ((a⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ twoOf (oE i)
    have h4 : a ^ 4 = 1 := by
      have := (List.mem_filter.mp ha).2
      rw [beq_iff_eq, ← colsN_pow_two_pow] at this
      exact (eq_one_iff_colsN _).mpr this
    have hinv : a⁻¹ = a * (a * a) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv,
        show a * (a * a) * a = a ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc], h4]
    rw [hinv, Units.val_mul, Units.val_mul, colsN_mul, colsN_mul]
    have hc := (oB_spec i (mem_zero_one hi)).2.2.2.1
    exact hc _ ha _ (hc _ ha _ ha)

theorem RS_le_OS {i : ℕ} (hi : i < 2) : RS i hi ≤ OS i :=
  fun u hu => (mem_OS_iff hi u).mpr (List.mem_filter.mp hu).1

theorem pow_four_of_RS {i : ℕ} (hi : i < 2)
    {u : GL (Fin 12) (ZMod 2)} (hu : u ∈ RS i hi) : u ^ 2 ^ 2 = 1 := by
  have := (List.mem_filter.mp hu).2
  rw [beq_iff_eq, ← colsN_pow_two_pow] at this
  exact (eq_one_iff_colsN _).mpr this

theorem card_OS_eq {i : ℕ} (hi : i < 2) :
    Nat.card (OS i) = 3 * Nat.card (RS i hi) := by
  have h := oB_spec i (mem_zero_one hi)
  have hsub := subB_spec h.1
  have hO : Nat.card (OS i) = (oE i).length :=
    card_genSubN_of h.1 (fun g hg => let ⟨u, _, hu⟩ := OS_gens_unit hi g hg; ⟨u, hu⟩)
  have hR : Nat.card (RS i hi) = (twoOf (oE i)).length := by
    refine card_of_cols (fun u => Iff.rfl) h.2.1
      (fun x hx => hsub.1 x (List.mem_filter.mp hx).1) fun x hx => ?_
    obtain ⟨u, -, hu⟩ := exists_OS_of hi (List.mem_filter.mp hx).1
    exact ⟨u, hu⟩
  rw [hO, hR]
  exact h.2.2.1

theorem RS_normal {i : ℕ} (hi : i < 2) :
    ((RS i hi).subgroupOf (OS i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hgn : ((g * n * g⁻¹ : ↥(OS i)) : GL (Fin 12) (ZMod 2)) ∈ OS i := (g * n * g⁻¹).2
  have h4 : ((g * n * g⁻¹ : ↥(OS i)) : GL (Fin 12) (ZMod 2)) ^ 2 ^ 2 = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, pow_four_of_RS hi hn, mul_one, mul_inv_cancel]
  refine List.mem_filter.mpr ⟨(mem_OS_iff hi _).mp hgn, ?_⟩
  rw [beq_iff_eq, ← colsN_pow_two_pow, h4, Units.val_one, colsN_one]

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
  have hxn : (x : GL (Fin 12) (ZMod 2)) ^ 2 ^ n = 1 := by
    have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥(OS i)) => ((y : ↥(OS i)) :
      GL (Fin 12) (ZMod 2))) hn
    simpa using this
  have hxM : (x : GL (Fin 12) (ZMod 2)) ∈ Mi i := OS_le_Mi hi x.2
  have h768 : orderOf (x : GL (Fin 12) (ZMod 2)) ∣ 768 := by
    rw [← card_Mi hi, ← Subgroup.orderOf_mk _ hxM]
    exact orderOf_dvd_natCard _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxn)
  have h256 : orderOf (x : GL (Fin 12) (ZMod 2)) ∣ 2 ^ 8 := by
    rw [hk] at h768 ⊢
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact hc.dvd_of_dvd_mul_right (by simpa using h768)
  have hx256 : (x : GL (Fin 12) (ZMod 2)) ^ 2 ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp h256
  rw [Subgroup.mem_subgroupOf]
  have hc := (mem_OS_iff hi _).mp x.2
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  rw [beq_iff_eq]
  refine (oB_spec i (mem_zero_one hi)).2.2.2.2.1 _ hc ?_
  rw [← colsN_pow_two_pow, hx256, Units.val_one, colsN_one]

theorem index_pCore_OS {i : ℕ} (hi : i < 2) :
    (CFSG.Open.pCore 2 ↥(OS i)).index = 3 := by
  rw [pCore_OS hi]
  have h := Subgroup.relIndex_mul_card (RS i hi) (OS i)
  rw [inf_eq_left.mpr (RS_le_OS hi), card_OS_eq hi] at h
  have hpos : 0 < Nat.card (RS i hi) := Nat.card_pos
  unfold Subgroup.relIndex at h
  nlinarith

theorem OS_sup_PM {i : ℕ} (hi : i < 2) : OS i ⊔ PM = Mi i := by
  have hle : OS i ⊔ PM ≤ Mi i := sup_le (OS_le_Mi hi) (PM_le_Mi i)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_Mi hi]
  have h3 : 3 ∣ Nat.card ↥(OS i ⊔ PM) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : OS i ≤ OS i ⊔ PM)
    rw [card_OS_eq hi] at this
    exact (Dvd.intro _ rfl).trans this
  have h256 : 256 ∣ Nat.card ↥(OS i ⊔ PM) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : PM ≤ OS i ⊔ PM)
    rwa [card_PM] at this
  have h768 : 768 ∣ Nat.card ↥(OS i ⊔ PM) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 256) h3 h256
  exact Nat.le_of_dvd Nat.card_pos h768

@[expose] def M12 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 m12G

theorem m12B_spec :
    subB 12 m12G m12E = true ∧ m12E.length = 2304 ∧
    (∀ x ∈ m12E, blkInvB blkA x = true ∧ blkInvB blkB x = true ∧
      blkPerm blkA x ∈ S7Cert.perm3L ∧ blkPerm blkB x ∈ S7Cert.perm3L) ∧
    (∀ l ∈ S7Cert.perm3L, ∀ l' ∈ S7Cert.perm3L, ∃ x ∈ m12E,
      blkPerm blkA x = l ∧ blkPerm blkB x = l') ∧
    ∀ x ∈ m12E, blkPerm blkA x = [0, 1, 2] → blkPerm blkB x = [0, 1, 2] → sqN x 2 = one12 := by
  have h := m22Check_parts.2.2.2.2.2.2.2.2.2
  simp only [m12B, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  refine ⟨a, b, fun x hx => ?_, fun l hl l' hl' => ?_, fun x hx h1 h2 => ?_⟩
  · obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := c x hx
    exact ⟨c1, c2, List.contains_iff_mem.mp c3, List.contains_iff_mem.mp c4⟩
  · simpa [List.any_eq_true] using d l hl l' hl'
  · have := e x hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact absurd h1 h
    · exact absurd h2 h
    · exact h

theorem mem_mRep {g : List ℕ} :
    g ∈ mRep ↔ g = mRep.getD 0 one12 ∨ g = mRep.getD 1 one12 := by
  have hlen : mRep.length = 2 := rfl
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hlen] at hi
    interval_cases i
    · exact Or.inl (List.getD_eq_getElem _ _ _).symm
    · exact Or.inr (List.getD_eq_getElem _ _ _).symm
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [hlen]; norm_num, (List.getD_eq_getElem _ _ _).symm⟩
    · exact ⟨1, by rw [hlen]; norm_num, (List.getD_eq_getElem _ _ _).symm⟩

theorem M12_gens_unit :
    ∀ g ∈ m12G, ∃ u ∈ m22, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Mi_gens_unit (i := 0) (by norm_num) g (List.mem_append_left _ hg)
  · rcases mem_mRep.mp hg with rfl | rfl
    · exact mRep_unit (by norm_num)
    · exact mRep_unit (by norm_num)

theorem mem_M12_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ M12 ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ m12E :=
  mem_genSubN_iff_of m12B_spec.1 (fun g hg => let ⟨u, _, hu⟩ := M12_gens_unit g hg; ⟨u, hu⟩) u

theorem sup_Mi : Mi 0 ⊔ Mi 1 = M12 := by
  apply le_antisymm
  · refine sup_le (Subgroup.closure_mono fun u hu => ?_) (Subgroup.closure_mono fun u hu => ?_)
    · rcases List.mem_append.mp hu with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (mem_mRep.mpr (Or.inl (List.mem_singleton.mp h)))
    · rcases List.mem_append.mp hu with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (mem_mRep.mpr (Or.inr (List.mem_singleton.mp h)))
  · refine (Subgroup.closure_le _).mpr fun u hu => ?_
    rcases List.mem_append.mp hu with h | h
    · exact Subgroup.mem_sup_left (PM_le_Mi 0 (Subgroup.subset_closure h))
    · rcases mem_mRep.mp h with h | h
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure
          (List.mem_append_right _ (List.mem_singleton.mpr h)))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure
          (List.mem_append_right _ (List.mem_singleton.mpr h)))

theorem blkPerm_one : blkPerm blkA one12 = [0, 1, 2] ∧ blkPerm blkB one12 = [0, 1, 2] := by
  decide +kernel

@[expose] noncomputable def chi :
    ↥M12 →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) where
  toFun x := (S7Cert.toPerm3 (blkPerm blkA (colsN ((x : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)))),
    S7Cert.toPerm3 (blkPerm blkB (colsN ((x : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)))))
  map_one' := by
    simp only [OneMemClass.coe_one, Units.val_one, colsN_one, blkPerm_one.1, blkPerm_one.2]
    rfl
  map_mul' x y := by
    have hx := (mem_M12_iff _).mp x.2
    have hy := (mem_M12_iff _).mp y.2
    obtain ⟨hxa, hxb, hxa', hxb'⟩ := m12B_spec.2.2.1 _ hx
    obtain ⟨-, -, hya', hyb'⟩ := m12B_spec.2.2.1 _ hy
    simp only [Subgroup.coe_mul, Units.val_mul, colsN_mul, blkPerm_mulN hxa hya',
      blkPerm_mulN hxb hyb', S7Cert.toPerm3_mul _ hxa' _ hya', S7Cert.toPerm3_mul _ hxb' _ hyb',
      Prod.mk_mul_mk]

theorem chi_surjective : Function.Surjective chi := by
  rintro ⟨σ, τ⟩
  obtain ⟨l, hl, rfl⟩ := S7Cert.toPerm3_surj σ
  obtain ⟨l', hl', rfl⟩ := S7Cert.toPerm3_surj τ
  obtain ⟨c, hc, hca, hcb⟩ := m12B_spec.2.2.2.1 l hl l' hl'
  obtain ⟨u, hu, hu'⟩ := exists_mem_of_elemsOf m12B_spec.1
    (fun g hg => let ⟨u, _, hu⟩ := M12_gens_unit g hg; ⟨u, hu⟩) hc
  have hcu : colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = c := by
    rw [hu', colsN_decN ((subB_spec m12B_spec.1).1 c hc)]
  refine ⟨⟨u, hu⟩, ?_⟩
  show (S7Cert.toPerm3 (blkPerm blkA (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)))),
    S7Cert.toPerm3 (blkPerm blkB (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))))) = _
  rw [hcu, hca, hcb]

theorem pow_four_of_chi {x : ↥M12} (h : chi x = 1) :
    (x : GL (Fin 12) (ZMod 2)) ^ 2 ^ 2 = 1 := by
  have hx := (mem_M12_iff _).mp x.2
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change S7Cert.toPerm3 (blkPerm blkA (colsN ((x : GL (Fin 12) (ZMod 2)) :
    Matrix (Fin 12) (Fin 12) (ZMod 2)))) = 1 at h1
  change S7Cert.toPerm3 (blkPerm blkB (colsN ((x : GL (Fin 12) (ZMod 2)) :
    Matrix (Fin 12) (Fin 12) (ZMod 2)))) = 1 at h2
  obtain ⟨-, -, ha, hb⟩ := m12B_spec.2.2.1 _ hx
  have hsq := m12B_spec.2.2.2.2 _ hx (S7Cert.toPerm3_eq_one _ ha h1)
    (S7Cert.toPerm3_eq_one _ hb h2)
  rw [eq_one_iff_colsN, colsN_pow_two_pow, hsq]

theorem M12_eq : M12 = OS 0 ⊔ OS 1 ⊔ PM := by
  rw [← sup_Mi, ← OS_sup_PM (i := 0) (by norm_num), ← OS_sup_PM (i := 1) (by norm_num)]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right)

end CFSG.Quasithin.H13.M22Cert
