module

public import CFSG.Quasithin.H13.L32NO3Model2
public import CFSG.Quasithin.H13.L32NS7Model3
public import CFSG.Quasithin.H13.L32NMatNGen

public section

namespace CFSG.Quasithin.H13.O3Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert

theorem colsOf_pow (u : GL (Fin 8) (ZMod 2)) (k : ℕ) :
    colsOf ((u ^ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      pow8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) k := by
  induction k with
  | zero => rw [pow_zero, Units.val_one, colsOf_one]; rfl
  | succ k ih => rw [pow_succ', Units.val_mul, colsOf_mul, ih]; rfl

theorem eq_one_of_colsOf {u : GL (Fin 8) (ZMod 2)}
    (h : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = one8) : u = 1 :=
  eq_of_colsOf_eq (by rw [h, Units.val_one, colsOf_one])

@[expose] def MM (c : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (pG c ++ [mRep c])

@[expose] def OM (c : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (oddOf (mE c))

theorem ovB_spec {c : ℕ} (hc : c < 2) :
    mRep c ∈ gamE c ∧ subB (pG c ++ [mRep c]) (mE c) = true ∧ (mE c).length = 3 * pOrd c ∧
    (∀ y ∈ gamE c, mv8 y (vS c) = vS c ∨
      (∃ p₁ ∈ pE c, mv8 p₁ (mv8 y (vS c)) ≠ mv8 y (vS c) ∧ ∃ p₂ ∈ pE c,
        mv8 p₂ (mv8 y (vS c)) ≠ mv8 y (vS c) ∧
          mv8 p₂ (mv8 y (vS c)) ≠ mv8 p₁ (mv8 y (vS c))) ∨
      y ∈ mE c ∨
      (3 * pOrd c < (elemsOf (pG c ++ [y]) (3 * pOrd c + 1)).length ∧
        nodupB (elemsOf (pG c ++ [y]) (3 * pOrd c + 1)) = true)) ∧
    subB (oddOf (mE c)) (oME c) = true ∧
    (∀ y ∈ oME c, mv8 y (vS c) ^^^ vS c ∈ [0, (wS c).1, (wS c).2]) ∧
    (∃ y ∈ oME c, mv8 y (vS c) ^^^ vS c = (wS c).1) ∧
    (∃ y ∈ oME c, mv8 y (vS c) ^^^ vS c = (wS c).2) ∧ (wS c).1 ^^^ (wS c).2 = vS c := by
  have h := (o3Check_parts.2.2 c (mem_zero_one hc)).2.2.2.1
  simp only [ovB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_filter, List.mem_range, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_, h5, h6, h7, h8, h9⟩
  rcases h4 y hy with ((h | ⟨-, p₁, hp₁, h11, p₂, hp₂, h12, h13⟩) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨p₁, hp₁, h11, p₂, hp₂, h12, h13⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mG_mem {c : ℕ} (hc : c < 2) :
    ∀ g ∈ pG c ++ [mRep c], g ∈ gamE c := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (pB_spec hc).2.2.1 g hg
  · rw [List.mem_singleton.mp hg]
    exact (ovB_spec hc).1

theorem mem_MM_iff {c : ℕ} (hc : c < 2) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ MM c ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ mE c :=
  mem_genSub_iff_of (ovB_spec hc).2.1 (unit_of_gamE hc (mG_mem hc)) u

theorem card_MM {c : ℕ} (hc : c < 2) :
    Nat.card (MM c) = 3 * pOrd c := by
  rw [MM, card_genSub_of (ovB_spec hc).2.1 (unit_of_gamE hc (mG_mem hc))]
  exact (ovB_spec hc).2.2.1

theorem PP_le_MM (c : ℕ) : PP c ≤ MM c :=
  Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem four_le_index {c : ℕ} (hc : c < 2) {M : Subgroup (GL (Fin 8) (ZMod 2))}
    (m : Fin 4 → ↥M)
    (hm : ∀ i j, ((m i : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (vec8 (vS c)) = ((m j : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (vec8 (vS c)) → i = j) :
    4 ≤ ((PP c).subgroupOf M).index := by
  have hinj : Function.Injective fun i =>
      (QuotientGroup.mk (m i) : ↥M ⧸ (PP c).subgroupOf M) := by
    intro i j h
    apply hm
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
    have h2 := PP_fix hc h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at h2
    rw [← Matrix.mulVec_mulVec] at h2
    calc ((m i : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c))
        = ((m i : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
            ((((m i)⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
              (((m j : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
                (vec8 (vS c)))) := by rw [h2]
      _ = _ := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Subgroup.index] using this

theorem mv8_inj_of {q : GL (Fin 8) (ZMod 2)} {x : List ℕ}
    (hq : (q : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x) {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : mv8 x a = mv8 x b) : a = b := by
  apply vec8_inj ha hb
  have h1 : (q : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 a) =
      (q : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 b) := by
    rw [hq, dec8_mulVec, dec8_mulVec, h]
  have h2 := congrArg (((q⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec) h1
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2

theorem sup_zpowers_eq {c : ℕ} (hc : c < 2)
    {M : Subgroup (GL (Fin 8) (ZMod 2))} (hPM : PP c ≤ M) (hcard : Nat.card M = 3 * pOrd c)
    {y : GL (Fin 8) (ZMod 2)} (hyM : y ∈ M) (hyP : y ∉ PP c) :
    PP c ⊔ Subgroup.zpowers y = M := by
  have hpos : 0 < pOrd c := by interval_cases c <;> decide
  have hK : PP c ⊔ Subgroup.zpowers y ≤ M := sup_le hPM (Subgroup.zpowers_le.mpr hyM)
  obtain ⟨t, ht⟩ : pOrd c ∣ Nat.card ↥(PP c ⊔ Subgroup.zpowers y) := by
    rw [← card_PP hc]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(PP c ⊔ Subgroup.zpowers y) ∣ 3 * pOrd c := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hK
  have h3 : t ≠ 1 := by
    rintro rfl
    apply hyP
    have : PP c = PP c ⊔ Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [ht, card_PP hc, mul_one]))
    rw [this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rw [ht, mul_comm 3] at h2
  have h4 : t ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos h2
  have hcard' : Nat.card ↥(PP c ⊔ Subgroup.zpowers y) = 3 * pOrd c := by
    rcases (Nat.dvd_prime (by norm_num)).mp h4 with h5 | h5
    · exact absurd h5 h3
    · rw [ht, h5, mul_comm]
  exact Subgroup.eq_of_le_of_card_ge hK (le_of_eq (by rw [hcard, hcard']))

theorem eq_MM_of {c : ℕ} (hc : c < 2)
    {M : Subgroup (GL (Fin 8) (ZMod 2))} (hMΓ : M ≤ gam c) (hPM : PP c ≤ M)
    (hcard : Nat.card M = 3 * pOrd c) {y : GL (Fin 8) (ZMod 2)} (hyM : y ∈ M)
    (hy : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) ≠ vec8 (vS c)) :
    M = MM c := by
  have hpos : 0 < pOrd c := by interval_cases c <;> decide
  have hidx : ((PP c).subgroupOf M).index = 3 := by
    have h := Subgroup.relIndex_mul_card (PP c) M
    rw [inf_eq_left.mpr hPM, card_PP hc, hcard] at h
    unfold Subgroup.relIndex at h
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hyΓ := (mem_gam_iff hc y).mp (hMΓ hyM)
  have hv : vS c < 256 := by interval_cases c <;> decide
  have hyP : y ∉ PP c := fun h => hy (PP_fix hc h)
  have hyv : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) =
      vec8 (mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c)) := mulVec_vec8 _ _
  have hu256 : mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c) < 256 :=
    mv8_lt (valid8_colsOf _) _
  have huv : mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c) ≠ vS c := fun h =>
    hy (by rw [hyv, h])
  rcases (ovB_spec hc).2.2.2.1 _ hyΓ with h | ⟨p₁, hp₁, h1, p₂, hp₂, h2, h12⟩ | h | ⟨hbig, hnd⟩
  · exact absurd h huv
  ·
    exfalso
    obtain ⟨q₁, hq₁, hq₁'⟩ := exists_mem_PP hc hp₁
    obtain ⟨q₂, hq₂, hq₂'⟩ := exists_mem_PP hc hp₂
    have hv₁ := (subB_spec (pB_spec hc).1).1 p₁ hp₁
    have hv₂ := (subB_spec (pB_spec hc).1).1 p₂ hp₂
    have hfix₁ : mv8 p₁ (vS c) = vS c := by
      have := PP_fix hc hq₁
      rw [hq₁', dec8_mulVec] at this
      exact vec8_inj (mv8_lt hv₁ _) hv this
    have hfix₂ : mv8 p₂ (vS c) = vS c := by
      have := PP_fix hc hq₂
      rw [hq₂', dec8_mulVec] at this
      exact vec8_inj (mv8_lt hv₂ _) hv this
    have hne₁ : mv8 p₁ (mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c)) ≠ vS c :=
      fun h => huv (mv8_inj_of hq₁' hu256 hv (by rw [h, hfix₁]))
    have hne₂ : mv8 p₂ (mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c)) ≠ vS c :=
      fun h => huv (mv8_inj_of hq₂' hu256 hv (by rw [h, hfix₂]))
    let m : Fin 4 → ↥M := ![1, ⟨y, hyM⟩, ⟨q₁ * y, M.mul_mem (hPM hq₁) hyM⟩,
      ⟨q₂ * y, M.mul_mem (hPM hq₂) hyM⟩]
    let cs : Fin 4 → ℕ := ![vS c, mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c),
      mv8 p₁ (mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c)),
      mv8 p₂ (mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) (vS c))]
    have hcs : ∀ i, ((m i : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (vec8 (vS c)) = vec8 (cs i) := by
      intro i
      fin_cases i
      · simp [m, cs]
      · exact hyv
      · show ((q₁ * y : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec _ = _
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyv, hq₁', dec8_mulVec]
        rfl
      · show ((q₂ * y : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec _ = _
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyv, hq₂', dec8_mulVec]
        rfl
    have hclt : ∀ i, cs i < 256 := by
      intro i
      fin_cases i
      · exact hv
      · exact hu256
      · exact mv8_lt hv₁ _
      · exact mv8_lt hv₂ _
    have hcinj : ∀ i j, cs i = cs j → i = j := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp only [cs] at h ⊢ <;> first
        | rfl
        | exact absurd h huv.symm | exact absurd h.symm huv.symm
        | exact absurd h hne₁.symm | exact absurd h.symm hne₁.symm
        | exact absurd h hne₂.symm | exact absurd h.symm hne₂.symm
        | exact absurd h h1.symm | exact absurd h.symm h1.symm
        | exact absurd h h2.symm | exact absurd h.symm h2.symm
        | exact absurd h h12.symm | exact absurd h.symm h12.symm
    have h4 := four_le_index hc m fun i j h => hcinj i j
      (vec8_inj (hclt i) (hclt j) (by rw [← hcs i, ← hcs j, h]))
    omega
  ·
    have hyMM : y ∈ MM c := (mem_MM_iff hc y).mpr h
    have hKM := sup_zpowers_eq hc hPM hcard hyM hyP
    have hKMM : PP c ⊔ Subgroup.zpowers y ≤ MM c :=
      sup_le (PP_le_MM c) (Subgroup.zpowers_le.mpr hyMM)
    rw [hKM] at hKMM
    exact Subgroup.eq_of_le_of_card_ge hKMM (le_of_eq (by rw [card_MM hc, hcard]))
  ·
    exfalso
    have hgval : ∀ g ∈ pG c ++ [colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))], Valid8 g := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact (subB_spec (pB_spec hc).1).2.2.2.2 g hg
      · rw [List.mem_singleton.mp hg]
        exact valid8_colsOf _
    have hgunit : ∀ g ∈ pG c ++ [colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))],
        ∃ u ∈ M, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨u, hu⟩ := unit_of_gamE hc (pB_spec hc).2.2.1 g hg
        exact ⟨u, hPM (mem_genSub_of_mem (subB_spec (pB_spec hc).1).2.2.2.2 hg hu), hu⟩
      · rw [List.mem_singleton.mp hg]
        exact ⟨y, hyM, (dec8_colsOf _).symm⟩
    have hgunit' : ∀ g ∈ pG c ++ [colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))],
        ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
      fun g hg => let ⟨u, _, hu⟩ := hgunit g hg; ⟨u, hu⟩
    have hKM : genSub (pG c ++ [colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))]) ≤ M := by
      refine (Subgroup.closure_le _).mpr fun u hu => ?_
      obtain ⟨v, hv', hv''⟩ := hgunit _ hu
      have : u = v := by
        apply Units.ext
        rw [hv'', dec8_colsOf]
      rw [this]
      exact hv'
    have hB : ∀ b ∈ elemsOf (pG c ++ [colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))])
        (3 * pOrd c + 1), ∃ u ∈ M, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 b := by
      intro b hb
      obtain ⟨w, rfl⟩ := mem_elemsOf hb
      obtain ⟨u, hu, hu'⟩ := exists_evalW _ hgval hgunit' w
      exact ⟨u, hKM hu, hu'⟩
    have hval : ∀ b ∈ elemsOf (pG c ++ [colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))])
        (3 * pOrd c + 1), Valid8 b := by
      intro b hb
      obtain ⟨w, rfl⟩ := mem_elemsOf hb
      exact valid8_evalW _ hgval w
    have := le_card_of_list (nodup_of_nodupB hnd) hB hval
    omega

theorem OM_gens_unit {c : ℕ} (hc : c < 2) :
    ∀ g ∈ oddOf (mE c), ∃ u ∈ MM c, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  intro g hg
  obtain ⟨w, rfl⟩ := mem_elemsOf (oddOf_sub g hg)
  exact exists_evalW _ (subB_spec (ovB_spec hc).2.1).2.2.2.2 (unit_of_gamE hc (mG_mem hc)) w

theorem OM_unit {c : ℕ} (hc : c < 2) :
    ∀ g ∈ oddOf (mE c), ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := OM_gens_unit hc g hg; ⟨u, hu⟩

theorem oTwoUpper_MM {c : ℕ} (hc : c < 2) :
    oTwoUpper (MM c) = OM c := by
  have hcard : Nat.card (MM c) = 2 ^ (if c = 0 then 5 else 6) * 3 := by
    rw [card_MM hc]
    interval_cases c <;> decide
  unfold oTwoUpper OM genSub
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine List.mem_filter.mpr ⟨(mem_MM_iff hc u).mp h1, ?_⟩
    rw [beq_iff_eq, ← colsOf_pow3, (MatNCert.odd_orderOf_iff_of_card hcard h1).mp h2,
      Units.val_one, colsOf_one]
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    have hu : u ∈ MM c := (mem_MM_iff hc u).mpr h1
    refine ⟨hu, (MatNCert.odd_orderOf_iff_of_card hcard hu).mpr ?_⟩
    rw [beq_iff_eq, ← colsOf_pow3, ← colsOf_one, ← Units.val_one] at h2
    exact eq_of_colsOf_eq h2

theorem OM_vec_eq {c : ℕ} (hc : c < 2) :
    (∃ y ∈ OM c, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) + vec8 (vS c) =
      vec8 (wS c).1) ∧
    (∃ y ∈ OM c, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) + vec8 (vS c) =
      vec8 (wS c).2) ∧ vec8 (wS c).1 + vec8 (wS c).2 = vec8 (vS c) := by
  have h := ovB_spec hc
  have hex : ∀ {x : List ℕ}, x ∈ oME c → ∃ u ∈ OM c,
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x := fun hx => by
    obtain ⟨w, rfl⟩ := mem_elemsOf hx
    exact exists_evalW _ (subB_spec h.2.2.2.2.1).2.2.2.2 (OM_unit hc) w
  refine ⟨?_, ?_, by rw [← vec8_xor, h.2.2.2.2.2.2.2.2]⟩
  · obtain ⟨x, hx, hxw⟩ := h.2.2.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := hex hx
    exact ⟨u, hu, by rw [hu', dec8_mulVec, ← vec8_xor, hxw]⟩
  · obtain ⟨x, hx, hxw⟩ := h.2.2.2.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := hex hx
    exact ⟨u, hu, by rw [hu', dec8_mulVec, ← vec8_xor, hxw]⟩

@[expose] def conjG (c : ℕ) : List (List ℕ) := (conjL c).map fun t => mul8 (mul8 t.1 t.2.2) t.2.1

theorem kB_spec {c : ℕ} (hc : c < 2) :
    kS c ∈ om3E ∧ mul8 (kS c) (kS c) = one8 ∧ b5N (mv8 (kS c) (vS c)) (vS c) = false ∧
    b5N (mv8 (kS c) (vS c)) (wS c).1 = true ∧
    (∀ t ∈ conjL c, t.1 ∈ om3E ∧ mul8 t.1 t.2.1 = one8 ∧ t.2.2 ∈ wE c) ∧
    subB (conjG c) (elemsOf (conjG c)) = true ∧ ∀ x ∈ om3E, x ∈ elemsOf (conjG c) := by
  have h := (o3Check_parts.2.2 c (mem_zero_one hc)).2.2.2.2.1
  simp only [kB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, fun t ht => let ⟨⟨a, b⟩, d⟩ := h5 t ht; ⟨a, b, d⟩, h6, h7⟩

theorem exists_mem_omega3 {x : List ℕ} (hx : x ∈ om3E) :
    ∃ u ∈ omega3, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hx
  rw [omega3_eq]
  exact exists_evalW _ (subB_spec basic_spec.1.1).2.2.2.2
    (unit_of_omNE fun g hg => gens_mem_omNE g (List.mem_append_left _ hg)) w

theorem exists_mem_WW {c : ℕ} (hc : c < 2) {x : List ℕ}
    (hx : x ∈ wE c) : ∃ w ∈ WW c, (w : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hx
  exact exists_evalW _ (subB_spec (wB_spec hc).2.1).2.2.2.2 (wG_unit hc) w

theorem kS_spec {c : ℕ} (hc : c < 2) :
    ∃ k ∈ omega3, k * k = 1 ∧
      b5V ((k : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c))) (vec8 (vS c)) = 0 ∧
      b5V ((k : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c))) (vec8 (wS c).1) = 1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := kB_spec hc
  obtain ⟨k, hk, hk'⟩ := exists_mem_omega3 h1
  have hval := (subB_spec basic_spec.1.1).1 _ h1
  have hkc : colsOf (k : Matrix (Fin 8) (Fin 8) (ZMod 2)) = kS c := by rw [hk', colsOf_dec8 hval]
  have hkv : (k : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) =
      vec8 (mv8 (kS c) (vS c)) := by rw [hk', dec8_mulVec]
  refine ⟨k, hk, eq_one_of_colsOf (by rw [Units.val_mul, colsOf_mul, hkc, h2]), ?_, ?_⟩
  · rw [hkv, ← b5N_spec, h3]
    rfl
  · rw [hkv, ← b5N_spec, h4]
    rfl

theorem omega3_le_conj {c : ℕ} (hc : c < 2) :
    omega3 ≤ Subgroup.closure
      {x | ∃ k ∈ omega3, ∃ w ∈ WW c, x = k * w * k⁻¹} := by
  obtain ⟨-, -, -, -, h5, h6, h7⟩ := kB_spec hc
  have hgen : ∀ g ∈ conjG c, ∃ x ∈ {x | ∃ k ∈ omega3, ∃ w ∈ WW c, x = k * w * k⁻¹},
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨ht1, ht2, ht3⟩ := h5 t ht
    obtain ⟨k, hk, hk'⟩ := exists_mem_omega3 ht1
    obtain ⟨w, hw, hw'⟩ := exists_mem_WW hc ht3
    have hlen : t.2.1.length = 8 := by rw [← length_mul8 t.1 t.2.1, ht2]; rfl
    have hwlen : t.2.2.length = 8 := ((subB_spec (wB_spec hc).2.1).1 _ ht3).1
    have hinv : dec8 t.2.1 = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      have h1 : (k : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 t.2.1 = 1 := by
        rw [hk', ← dec8_mul8 _ _ hlen, ht2, dec8_one8]
      calc dec8 t.2.1
          = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
              ((k : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 t.2.1) := by
            rw [Units.inv_mul_cancel_left]
        _ = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
            rw [h1, mul_one]
    refine ⟨k * w * k⁻¹, ⟨k, hk, w, hw, rfl⟩, ?_⟩
    rw [dec8_mul8 _ _ hlen, dec8_mul8 _ _ hwlen, Units.val_mul, Units.val_mul, hk', hw', hinv]
  have hle : genSub (conjG c) ≤
      Subgroup.closure {x | ∃ k ∈ omega3, ∃ w ∈ WW c, x = k * w * k⁻¹} := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    obtain ⟨x, hx, hx'⟩ := hgen _ hu
    have : u = x := Units.ext (by rw [hx', dec8_colsOf])
    rw [this]
    exact Subgroup.subset_closure hx
  have hunit : ∀ g ∈ conjG c, ∃ v : GL (Fin 8) (ZMod 2),
      (v : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
    fun g hg => let ⟨x, _, hx⟩ := hgen g hg; ⟨x, hx⟩
  intro u hu
  exact hle ((mem_genSub_iff_of h6 hunit u).mpr (h7 _ ((mem_omega3_iff u).mp hu)))

@[expose] def cenL (c : ℕ) (i : List ℕ) : List (List ℕ) :=
  (gamE c).filter fun x => mul8 x i == mul8 i x

@[expose] def cenAg (c : ℕ) (i : List ℕ) : List (List ℕ) :=
  (cenL c i).filter fun x => pow8 x 15 == one8

@[expose] def cenA (c : ℕ) (i : GL (Fin 8) (ZMod 2)) : Subgroup (GL (Fin 8) (ZMod 2)) :=
  genSub (cenAg c (colsOf (i : Matrix (Fin 8) (Fin 8) (ZMod 2))))

theorem cenB_spec {c : ℕ} (hc : c < 2) :
    ∀ i ∈ wE c, i ∈ om3E ∨
      (subB (cenAg c i) (elemsOf (cenAg c i)) = true ∧ (elemsOf (cenAg c i)).length = 60 ∧
        ∀ x ∈ cenL c i, x = one8 ∨ x = i ∨ pow8 x 16 ≠ one8 ∨
          ∃ a ∈ cenAg c i, pow8 (mul8 (mul8 (pow8 x 15) (pow8 a 14)) (mul8 x a)) 15 = one8 ∧
            mul8 (mul8 (pow8 x 15) (pow8 a 14)) (mul8 x a) ≠ one8) := by
  have h := (o3Check_parts.2.2 c (mem_zero_one hc)).2.2.2.2.2
  simp only [cenB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    List.any_eq_true] at h
  intro i hi
  rcases h i hi with h1 | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h1, h2, fun x hx => ?_⟩
    rcases h3 x hx with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem cenAg_sub {c : ℕ} {i x : List ℕ} (hx : x ∈ cenAg c i) :
    x ∈ gamE c ∧ mul8 x i = mul8 i x ∧ pow8 x 15 = one8 := by
  obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
  obtain ⟨hx3, hx4⟩ := List.mem_filter.mp hx1
  exact ⟨hx3, beq_iff_eq.mp hx4, beq_iff_eq.mp hx2⟩

theorem cenAg_unit {c : ℕ} (hc : c < 2) (i : List ℕ) :
    ∀ g ∈ cenAg c i, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  unit_of_gamE hc fun _ hg => (cenAg_sub hg).1

theorem exists_cols_gam {c : ℕ} (hc : c < 2) {x : List ℕ}
    (hx : x ∈ gamE c) :
    ∃ u ∈ gam c, colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = x := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_gam hc hx
  exact ⟨u, hu, by rw [hu', colsOf_dec8 ((subB_spec basic_spec.2.2.1.1).1 _
    (gamE_mem_omNE hc hx))]⟩

theorem comm_of_cols {u v : GL (Fin 8) (ZMod 2)}
    (h : mul8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))
      (colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2))) =
      mul8 (colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2)))
        (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))) : u * v = v * u :=
  eq_of_colsOf_eq (by rw [Units.val_mul, colsOf_mul, Units.val_mul, colsOf_mul, h])

theorem card_cenA {c : ℕ} (hc : c < 2) {i : GL (Fin 8) (ZMod 2)}
    (hiW : i ∈ WW c) (hi3 : i ∉ omega3) : Nat.card (cenA c i) = 60 := by
  rcases cenB_spec hc _ ((mem_WW_iff hc i).mp hiW) with h | ⟨h1, h2, -⟩
  · exact absurd ((mem_omega3_iff i).mpr h) hi3
  · rw [cenA, card_genSub_of h1 (cenAg_unit hc _)]
    exact h2

theorem cenA_le {c : ℕ} (hc : c < 2) (i : GL (Fin 8) (ZMod 2)) :
    cenA c i ≤ gam c ⊓ Subgroup.centralizer ({i} : Set (GL (Fin 8) (ZMod 2))) := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨h1, h2, -⟩ := cenAg_sub hu
  exact ⟨(mem_gam_iff hc u).mpr h1, Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_cols h2)⟩

theorem mem_cenA {c : ℕ} (hc : c < 2) {i a : GL (Fin 8) (ZMod 2)}
    (ha : a ∈ gam c) (hai : a * i = i * a) (ha15 : a ^ 15 = 1) : a ∈ cenA c i := by
  refine Subgroup.subset_closure (List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨(mem_gam_iff hc a).mp ha, ?_⟩, ?_⟩)
  · rw [beq_iff_eq, ← colsOf_mul, ← colsOf_mul, ← Units.val_mul, ← Units.val_mul, hai]
  · rw [beq_iff_eq, ← colsOf_pow, ha15, Units.val_one, colsOf_one]

theorem cen_spec {c : ℕ} (hc : c < 2) {i : GL (Fin 8) (ZMod 2)}
    (hiW : i ∈ WW c) (hi3 : i ∉ omega3) {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ gam c)
    (hxi : x * i = i * x) (hx16 : x ^ 16 = 1) (hx1 : x ≠ 1) (hxi' : x ≠ i) :
    ∃ a ∈ gam c, a * i = i * a ∧ a ^ 15 = 1 ∧ (x⁻¹ * a⁻¹ * (x * a)) ^ 15 = 1 ∧
      x⁻¹ * a⁻¹ * (x * a) ≠ 1 := by
  rcases cenB_spec hc _ ((mem_WW_iff hc i).mp hiW) with h | ⟨-, -, h⟩
  · exact absurd ((mem_omega3_iff i).mpr h) hi3
  have hxC : colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈
      cenL c (colsOf (i : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
    refine List.mem_filter.mpr ⟨(mem_gam_iff hc x).mp hx, ?_⟩
    rw [beq_iff_eq, ← colsOf_mul, ← colsOf_mul, ← Units.val_mul, ← Units.val_mul, hxi]
  rcases h _ hxC with h | h | h | ⟨a', ha', h15, hne⟩
  · exact absurd (eq_one_of_colsOf h) hx1
  · exact absurd (eq_of_colsOf_eq h) hxi'
  · exact absurd (by rw [← colsOf_pow, hx16, Units.val_one, colsOf_one]) h
  obtain ⟨ha'Γ, ha'i, ha'15⟩ := cenAg_sub ha'
  obtain ⟨a, haΓ, hva⟩ := exists_cols_gam hc ha'Γ
  have ha15 : a ^ 15 = 1 := eq_one_of_colsOf (by rw [colsOf_pow, hva, ha'15])
  have hxinv : x⁻¹ = x ^ 15 :=
    inv_eq_of_mul_eq_one_right (by rw [show x * x ^ 15 = x ^ 16 by rw [← pow_succ']]; exact hx16)
  have hainv : a⁻¹ = a ^ 14 :=
    inv_eq_of_mul_eq_one_right (by rw [show a * a ^ 14 = a ^ 15 by rw [← pow_succ']]; exact ha15)
  have hcm : colsOf
      ((x⁻¹ * a⁻¹ * (x * a) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      mul8 (mul8 (pow8 (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) 15) (pow8 a' 14))
        (mul8 (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) a') := by
    rw [hxinv, hainv, Units.val_mul, colsOf_mul, Units.val_mul, colsOf_mul, colsOf_pow,
      colsOf_pow, Units.val_mul, colsOf_mul, hva]
  refine ⟨a, haΓ, comm_of_cols (by rw [hva, ha'i]), ha15,
    eq_one_of_colsOf (by rw [colsOf_pow, hcm, h15]), fun h1 => hne ?_⟩
  rw [← hcm, h1, Units.val_one, colsOf_one]

end CFSG.Quasithin.H13.O3Cert
