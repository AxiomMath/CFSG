module

public import CFSG.Quasithin.H13.L32NM22Model2
public import CFSG.Quasithin.H13.L32NS7Model3

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert L1442M CFSG.Quasithin

@[expose] def OS (i : ℕ) : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 (oddOf (mE i))

theorem oB_spec :
    ∀ i ∈ [0, 1], subB 12 (oG i) (oE i) = true ∧ (twoOf (oE i)).Nodup ∧
      (oE i).length = 3 * (twoOf (oE i)).length ∧
      (∀ a ∈ twoOf (oE i), ∀ b ∈ twoOf (oE i), mulN a b ∈ twoOf (oE i)) ∧
      (∀ o ∈ oE i, sqN o 8 = one12 → sqN o 2 = one12) ∧
      (∀ y ∈ oE i, mvN y v0 ^^^ v0 ∈ [0, (oWs.getD i (0, 0)).1, (oWs.getD i (0, 0)).2,
        (oWs.getD i (0, 0)).1 ^^^ (oWs.getD i (0, 0)).2]) ∧
      (∃ y ∈ oE i, mvN y v0 ^^^ v0 = (oWs.getD i (0, 0)).1) ∧
      (∃ y ∈ oE i, mvN y v0 ^^^ v0 = (oWs.getD i (0, 0)).2) ∧
      (∃ y ∈ oE i, ∃ v ∈ List.range 4096,
        polN 12 q12c (mvN y v ^^^ v) (oWs.getD i (0, 0)).1 = true) ∧
      (∀ g ∈ oG i, powN 12 g 3 = one12) ∧ ∀ x ∈ oddOf (mE i), x ∈ oE i := by
  have h := m22Check_parts.2.2.2.2.2.2.2.2.1
  simp only [oB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  intro i hi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, a2⟩, a3⟩, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩ := h i hi
  refine ⟨a, nodup_of_nodupB b, c, fun x hx y hy => ?_, fun o ho h8 => ?_, fun y hy => ?_, ?_, ?_,
    ?_, a2, fun x hx => ?_⟩
  · simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using d x hx y hy
  · have := e o ho
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at this
    exact this.resolve_left (not_not.mpr h8)
  · simpa [List.contains_iff_mem] using f y hy
  · simpa [List.any_eq_true] using g
  · simpa [List.any_eq_true] using k
  · obtain ⟨y, hy, h1⟩ := List.any_eq_true.mp l
    exact ⟨y, hy, 1, List.mem_range.mpr (by norm_num), h1⟩
  · simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using a3 x hx

theorem mem_zero_one {i : ℕ} (hi : i < 2) : i ∈ [0, 1] := by
  interval_cases i <;> simp

theorem oddOf_sub {M : List (List ℕ)} : ∀ x ∈ oddOf M, x ∈ M := fun _ hx =>
  (List.mem_filter.mp hx).1

theorem OS_gens_unit {i : ℕ} (hi : i < 2) :
    ∀ g ∈ oddOf (mE i), ∃ u ∈ Mi i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  exact exists_mem_Mi hi (oddOf_sub g hg)

theorem OS_le_Mi {i : ℕ} (hi : i < 2) : OS i ≤ Mi i := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  exact (mem_Mi_iff hi u).mpr (oddOf_sub _ hu)

theorem oG_unit {i : ℕ} (hi : i < 2) :
    ∀ g ∈ oG i, ∃ u ∈ Mi i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  have hg' : g ∈ (oW.getD i []).map (evalW 12 (pG ++ [mRep.getD i one12])) := hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg'
  exact exists_evalW _ (Mi_gens_valid hi) (Mi_gens_unit' hi) w

theorem oG_unit' {i : ℕ} (hi : i < 2) :
    ∀ g ∈ oG i, ∃ u : GL (Fin 12) (ZMod 2), (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := oG_unit hi g hg; ⟨u, hu⟩

theorem OS_eq {i : ℕ} (hi : i < 2) : OS i = genSubN 12 (oG i) := by
  have h := oB_spec i (mem_zero_one hi)
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun u hu => ?_
    exact (mem_genSubN_iff_of h.1 (oG_unit' hi) u).mpr (h.2.2.2.2.2.2.2.2.2.2 _ hu)
  · refine (Subgroup.closure_le _).mpr fun u hu => ?_
    have hu' : colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ oG i := hu
    obtain ⟨u', hu'M, hu'v⟩ := oG_unit hi _ hu'
    have he : u = u' := Units.ext (by rw [hu'v, decN_colsN])
    refine Subgroup.subset_closure (List.mem_filter.mpr ⟨(mem_Mi_iff hi u).mp (he ▸ hu'M), ?_⟩)
    rw [beq_iff_eq]
    exact h.2.2.2.2.2.2.2.2.2.1 _ hu'

theorem mem_OS_iff {i : ℕ} (hi : i < 2) (u : GL (Fin 12) (ZMod 2)) :
    u ∈ OS i ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ oE i := by
  rw [OS_eq hi]
  exact mem_genSubN_iff_of (oB_spec i (mem_zero_one hi)).1 (oG_unit' hi) u

theorem exists_OS_of {i : ℕ} (hi : i < 2) {c : List ℕ}
    (hc : c ∈ oE i) : ∃ u ∈ OS i, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c := by
  rw [OS_eq hi]
  exact exists_mem_of_elemsOf (oB_spec i (mem_zero_one hi)).1 (oG_unit' hi) hc

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
  obtain ⟨c, hc, v, -, hv⟩ := h.2.2.2.2.2.2.2.2.1
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
  have hO : Nat.card (OS i) = (oE i).length := by
    rw [OS_eq hi]
    exact card_genSubN_of h.1 (oG_unit' hi)
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
    (∀ c ∈ m12Cos, ValidN 12 c.2 ∧ mulN c.1 c.2 = one12) ∧
    (∃ c ∈ m12Cos, mulN c.2 one12 ∈ pE) ∧
    (∀ g ∈ m12G, ∀ c ∈ m12Cos, ∃ c' ∈ m12Cos, mulN c'.2 (mulN g c.1) ∈ pE) ∧
    (∀ c ∈ m12Cos, blkInvB blkA c.1 = true ∧ blkInvB blkB c.1 = true ∧
      blkPerm blkA c.1 ∈ S7Cert.perm3L ∧ blkPerm blkB c.1 ∈ S7Cert.perm3L) ∧
    (∀ x ∈ pE, blkInvB blkA x = true ∧ blkInvB blkB x = true ∧
      blkPerm blkA x ∈ S7Cert.perm3L ∧ blkPerm blkB x ∈ S7Cert.perm3L) ∧
    (∀ l ∈ S7Cert.perm3L, ∀ l' ∈ S7Cert.perm3L, ∃ t ∈ m12SurW, t.1 = l ∧ t.2.1 = l') ∧
    (∀ t ∈ m12SurW, blkPerm blkA (evalW 12 m12G t.2.2) = t.1 ∧
      blkPerm blkB (evalW 12 m12G t.2.2) = t.2.1) ∧
    ∀ c ∈ m12Cos, ∀ p ∈ pE, S7Cert.compL (blkPerm blkA c.1) (blkPerm blkA p) = [0, 1, 2] →
      S7Cert.compL (blkPerm blkB c.1) (blkPerm blkB p) = [0, 1, 2] →
      sqN (mulN c.1 p) 2 = one12 := by
  have h := m22Check_parts.2.2.2.2.2.2.2.2.2
  simp only [m12B, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun c hc => ⟨validB_iff.mp (h1 c hc).1, (h1 c hc).2⟩, h2, h3, fun c hc => ?_,
    fun x hx => ?_, h6, h7, fun c hc p hp e1 e2 => ?_⟩
  · obtain ⟨⟨⟨a, b⟩, c'⟩, d⟩ := h4 c hc
    exact ⟨a, b, c', d⟩
  · obtain ⟨⟨⟨a, b⟩, c'⟩, d⟩ := h5 x hx
    exact ⟨a, b, c', d⟩
  · have := h8 c hc p hp
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact absurd e1 h
    · exact absurd e2 h
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

theorem M12_gens_valid : ∀ g ∈ m12G, ValidN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (subB_spec pB_spec.1).2.2.2.2 g hg
  · rcases mem_mRep.mp hg with rfl | rfl
    · exact validN_mRep (by norm_num)
    · exact validN_mRep (by norm_num)

theorem M12_gens_unit' : ∀ g ∈ m12G, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := M12_gens_unit g hg; ⟨u, hu⟩

theorem exists_M12_of_evalW (w : List ℕ) :
    ∃ u ∈ M12, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (evalW 12 m12G w) :=
  exists_evalW m12G M12_gens_valid M12_gens_unit' w

theorem m12Cos_unit {c : List ℕ × List ℕ} (hc : c ∈ m12Cos) :
    ValidN 12 c.1 ∧ ∃ u ∈ M12, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.1 ∧
      ((u⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.2 := by
  have hv := m12B_spec.1 c hc
  have hz : c ∈ (m12CosW.map (evalW 12 m12G)).zip m12Inv := hc
  obtain ⟨w, -, hw⟩ := List.mem_map.mp (List.of_mem_zip hz).1
  obtain ⟨u, hu, hu'⟩ := exists_M12_of_evalW w
  have hv1 : ValidN 12 c.1 := by
    rw [← hw]
    exact validN_evalW _ M12_gens_valid w
  have hu1 : (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.1 := by
    rw [← hw]
    exact hu'
  exact ⟨hv1, u, hu, hu1, inv_val_of hv1 hv.1 hu1 hv.2⟩

theorem exists_m12Cos_of_mem_M12 {u : GL (Fin 12) (ZMod 2)} (hu : u ∈ M12) :
    ∃ c ∈ m12Cos, mulN c.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
  obtain ⟨hv, ho, hg, -⟩ := m12B_spec
  have key : ∀ c ∈ m12Cos, ∀ cu : GL (Fin 12) (ZMod 2),
      ((cu⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.2 →
      ∀ y : GL (Fin 12) (ZMod 2),
        (cu⁻¹ * y ∈ PM ↔ mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) := by
    intro c hc cu hcu y
    rw [mem_PM_iff, Units.val_mul, colsN_mul, hcu, colsN_decN (hv c hc).1]
  have hstep : ∀ s : GL (Fin 12) (ZMod 2),
      colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ m12G → ∀ y : GL (Fin 12) (ZMod 2),
        (∃ c ∈ m12Cos, mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) →
        ∃ c ∈ m12Cos, mulN c.2
          (colsN ((s * y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
    rintro s hs y ⟨c, hc, hcy⟩
    obtain ⟨c', hc', hc's⟩ := hg _ hs c hc
    obtain ⟨hv1, cu, -, hcu1, hcu2⟩ := m12Cos_unit hc
    obtain ⟨-, cu', -, -, hcu'2⟩ := m12Cos_unit hc'
    refine ⟨c', hc', (key c' hc' cu' hcu'2 _).mp ?_⟩
    have e : cu'⁻¹ * (s * y) = (cu'⁻¹ * (s * cu)) * (cu⁻¹ * y) := by group
    rw [e]
    refine PM.mul_mem ((key c' hc' cu' hcu'2 _).mpr ?_) ((key c hc cu hcu2 y).mpr hcy)
    rw [Units.val_mul, colsN_mul, hcu1, colsN_decN hv1]
    exact hc's
  have hpow : ∀ s : GL (Fin 12) (ZMod 2),
      colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ m12G → ∀ (m : ℕ) (y : GL (Fin 12) (ZMod 2)),
      (∃ c ∈ m12Cos, mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) →
      ∃ c ∈ m12Cos, mulN c.2
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
  unfold M12 genSubN at hu
  refine Subgroup.closure_induction_left (p := fun (u : GL (Fin 12) (ZMod 2)) _ =>
    ∃ c ∈ m12Cos, mulN c.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) ?_ ?_ ?_ hu
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

theorem exists_m12Cos_mul {u : GL (Fin 12) (ZMod 2)} (hu : u ∈ M12) :
    ∃ c ∈ m12Cos, ∃ q ∈ pE, colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = mulN c.1 q := by
  obtain ⟨c, hc, hq⟩ := exists_m12Cos_of_mem_M12 hu
  obtain ⟨hv1, cu, -, hcu1, hcu2⟩ := m12Cos_unit hc
  refine ⟨c, hc, _, hq, ?_⟩
  calc colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))
      = colsN ((cu * (cu⁻¹ * u) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
        rw [mul_inv_cancel_left]
    _ = _ := by
        rw [Units.val_mul, colsN_mul, Units.val_mul, colsN_mul, hcu1, hcu2, colsN_decN hv1,
          colsN_decN (m12B_spec.1 c hc).1]

theorem blkInvB_mulN {blks : List (List ℕ)} {x y : List ℕ} (hx : blkInvB blks x = true)
    (hy : blkInvB blks y = true) (hyp : blkPerm blks y ∈ S7Cert.perm3L) :
    blkInvB blks (mulN x y) = true := by
  have key : ∀ i < 3, ∀ v, blkOf blks (mvN y v) = (blkPerm blks y).getD i 0 →
      blkOf blks (mvN (mulN x y) v) =
        blkOf blks (mvN x ((blks.getD ((blkPerm blks y).getD i 0) []).getD 0 0)) := by
    intro i hi v hv
    have hj3 := getD_lt_of_perm3L hyp hi
    rw [mvN_mulN, blkInvB_spec hx hj3 (mem_of_blkOf hv hj3)]
  simp only [blkInvB, List.all_eq_true, beq_iff_eq]
  intro i hi v hv
  have hi3 : i < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  rw [key i hi3 v (by rw [blkInvB_spec hy hi3 hv, getD_blkPerm blks y hi3 0]),
    getD_blkPerm blks (mulN x y) hi3 3, key i hi3 _ (getD_blkPerm blks y hi3 0).symm]

theorem perm3L_compL :
    ∀ l ∈ S7Cert.perm3L, ∀ l' ∈ S7Cert.perm3L, S7Cert.compL l l' ∈ S7Cert.perm3L := by
  decide

theorem blk_mulN {x y : List ℕ}
    (hx : blkInvB blkA x = true ∧ blkInvB blkB x = true ∧
      blkPerm blkA x ∈ S7Cert.perm3L ∧ blkPerm blkB x ∈ S7Cert.perm3L)
    (hy : blkInvB blkA y = true ∧ blkInvB blkB y = true ∧
      blkPerm blkA y ∈ S7Cert.perm3L ∧ blkPerm blkB y ∈ S7Cert.perm3L) :
    blkInvB blkA (mulN x y) = true ∧ blkInvB blkB (mulN x y) = true ∧
      blkPerm blkA (mulN x y) ∈ S7Cert.perm3L ∧ blkPerm blkB (mulN x y) ∈ S7Cert.perm3L := by
  obtain ⟨xa, xb, xa', xb'⟩ := hx
  obtain ⟨ya, yb, ya', yb'⟩ := hy
  refine ⟨blkInvB_mulN xa ya ya', blkInvB_mulN xb yb yb', ?_, ?_⟩
  · rw [blkPerm_mulN xa ya']
    exact perm3L_compL _ xa' _ ya'
  · rw [blkPerm_mulN xb yb']
    exact perm3L_compL _ xb' _ yb'

theorem blk_of_mem_M12 {u : GL (Fin 12) (ZMod 2)} (hu : u ∈ M12) :
    blkInvB blkA (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) = true ∧
      blkInvB blkB (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) = true ∧
      blkPerm blkA (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ S7Cert.perm3L ∧
      blkPerm blkB (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ S7Cert.perm3L := by
  obtain ⟨c, hc, q, hq, he⟩ := exists_m12Cos_mul hu
  rw [he]
  exact blk_mulN (m12B_spec.2.2.2.1 c hc) (m12B_spec.2.2.2.2.1 q hq)

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
    obtain ⟨hxa, hxb, hxa', hxb'⟩ := blk_of_mem_M12 x.2
    obtain ⟨-, -, hya', hyb'⟩ := blk_of_mem_M12 y.2
    simp only [Subgroup.coe_mul, Units.val_mul, colsN_mul, blkPerm_mulN hxa hya',
      blkPerm_mulN hxb hyb', S7Cert.toPerm3_mul _ hxa' _ hya', S7Cert.toPerm3_mul _ hxb' _ hyb',
      Prod.mk_mul_mk]

theorem chi_surjective : Function.Surjective chi := by
  rintro ⟨σ, τ⟩
  obtain ⟨l, hl, rfl⟩ := S7Cert.toPerm3_surj σ
  obtain ⟨l', hl', rfl⟩ := S7Cert.toPerm3_surj τ
  obtain ⟨t, ht, rfl, rfl⟩ := m12B_spec.2.2.2.2.2.1 l hl l' hl'
  obtain ⟨u, hu, hu'⟩ := exists_M12_of_evalW t.2.2
  have hcu : colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = evalW 12 m12G t.2.2 := by
    rw [hu', colsN_decN (validN_evalW _ M12_gens_valid _)]
  refine ⟨⟨u, hu⟩, ?_⟩
  change (S7Cert.toPerm3 (blkPerm blkA (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)))),
    S7Cert.toPerm3 (blkPerm blkB (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))))) = _
  rw [hcu, (m12B_spec.2.2.2.2.2.2.1 t ht).1, (m12B_spec.2.2.2.2.2.2.1 t ht).2]

theorem pow_four_of_chi {x : ↥M12} (h : chi x = 1) :
    (x : GL (Fin 12) (ZMod 2)) ^ 2 ^ 2 = 1 := by
  obtain ⟨c, hc, q, hq, he⟩ := exists_m12Cos_mul x.2
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change S7Cert.toPerm3 (blkPerm blkA (colsN ((x : GL (Fin 12) (ZMod 2)) :
    Matrix (Fin 12) (Fin 12) (ZMod 2)))) = 1 at h1
  change S7Cert.toPerm3 (blkPerm blkB (colsN ((x : GL (Fin 12) (ZMod 2)) :
    Matrix (Fin 12) (Fin 12) (ZMod 2)))) = 1 at h2
  obtain ⟨-, -, ha, hb⟩ := blk_of_mem_M12 x.2
  have hca := m12B_spec.2.2.2.1 c hc
  have hqa := m12B_spec.2.2.2.2.1 q hq
  have e1 := S7Cert.toPerm3_eq_one _ ha h1
  have e2 := S7Cert.toPerm3_eq_one _ hb h2
  rw [he, blkPerm_mulN hca.1 hqa.2.2.1] at e1
  rw [he, blkPerm_mulN hca.2.1 hqa.2.2.2] at e2
  rw [eq_one_iff_colsN, colsN_pow_two_pow, he, m12B_spec.2.2.2.2.2.2.2 c hc q hq e1 e2]

theorem M12_eq : M12 = OS 0 ⊔ OS 1 ⊔ PM := by
  rw [← sup_Mi, ← OS_sup_PM (i := 0) (by norm_num), ← OS_sup_PM (i := 1) (by norm_num)]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right)

end CFSG.Quasithin.H13.M22Cert
