module

public import CFSG.Quasithin.H13.L32NMatNGen
public import Certificates.Certificate7189

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert L1442M

theorem m22Check_eq : m22Check = true :=
  Certificates.certificate7189

theorem m22Check_parts :
    gG.all (validB 12) = true ∧ orbB = true ∧ s0B = true ∧ schB = true ∧ pB = true ∧
      e0B = true ∧ witB = true ∧ ovB = true ∧ oB = true ∧ m12B = true := by
  have h := m22Check_eq
  simp only [m22Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem gG_cols : gG = [colsN (m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)),
    colsN (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2))] := by
  decide +kernel

theorem validN_gG : ∀ g ∈ gG, ValidN 12 g := by
  rw [gG_cols]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact validN_colsN _

@[expose] def gU (i : ℕ) : GL (Fin 12) (ZMod 2) :=
  if i = 0 then m22a else if i = 1 then m22b else 1

@[expose] def tU (w : List ℕ) : GL (Fin 12) (ZMod 2) := (w.map gU).prod

theorem gU_val (i : ℕ) : ((gU i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
    decN 12 (gG.getD i one12) := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i <;> rw [gG_cols] <;> simp [gU, decN_colsN]
  · rw [List.getD_eq_default _ _ (by simp [gG]; omega), decN_oneN]
    simp [gU, show i ≠ 0 by omega, show i ≠ 1 by omega]

theorem tU_cons (i : ℕ) (w : List ℕ) : tU (i :: w) = gU i * tU w := by
  simp only [tU, List.map_cons, List.prod_cons]

theorem tU_val (w : List ℕ) :
    ((tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (tW w) := by
  induction w with
  | nil =>
    simp only [tU, List.map_nil, List.prod_nil, Units.val_one]
    exact decN_oneN.symm
  | cons i w ih =>
    rw [tU_cons, Units.val_mul, ih, gU_val]
    show _ = decN 12 (evalW 12 gG (i :: w))
    rw [evalW_cons, decN_mulN (validN_getD validN_gG i).1 (length_evalW gG w)]

theorem gU_mem (i : ℕ) : gU i ∈ m22 := by
  unfold gU
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact one_mem _

theorem tU_mem (w : List ℕ) : tU w ∈ m22 := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    rw [tU_cons]
    exact mul_mem (gU_mem i) ih

theorem orbB_spec :
    orbL.head? = some (v0, []) ∧ orbL.length = 693 ∧ (orbL.map Prod.fst).Nodup ∧
      ∀ uw ∈ orbL, mvN (tW uw.2) v0 = uw.1 := by
  have h := m22Check_parts.2.1
  simp only [orbB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  have h5 : ((orbL.map Prod.fst).mergeSort).Nodup :=
    (List.isChain_iff_pairwise.mp h3).imp (fun hab => ne_of_lt hab)
  exact (List.mergeSort_perm _ _).nodup_iff.mp h5

theorem v0_mem : (v0, ([] : List ℕ)) ∈ orbL :=
  List.mem_of_mem_head? (by rw [orbB_spec.1]; rfl)

theorem orbL_lt {uw : ℕ × List ℕ} (huw : uw ∈ orbL) :
    uw.1 < 2 ^ 12 := by
  rw [← orbB_spec.2.2.2 uw huw]
  exact mvN_lt (validN_evalW gG validN_gG _).2 _

theorem orbL_ext {uw uw' : ℕ × List ℕ} (huw : uw ∈ orbL)
    (huw' : uw' ∈ orbL) (h : uw.1 = uw'.1) : uw = uw' :=
  List.inj_on_of_nodup_map orbB_spec.2.2.1 huw huw' h

theorem mem_orbL_of_mem_getD {k : ℕ} {x : ℕ × List ℕ}
    (hx : x ∈ ((List.range 64).map fun b => orbL.filter fun p => p.1 % 64 == b).getD k []) :
    x ∈ orbL := by
  rw [List.getD_eq_getElem?_getD] at hx
  cases hk : ((List.range 64).map fun b => orbL.filter fun p => p.1 % 64 == b)[k]? with
  | none => simp [hk] at hx
  | some M =>
    rw [hk, Option.getD_some] at hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hk)
    exact (List.mem_filter.mp hx).1

theorem schB_spec :
    ∀ uw ∈ orbL, ∀ g ∈ gG, ∃ uw' ∈ orbL, uw'.1 = mvN g uw.1 ∧
      ∃ s : List ℕ, s.length = 12 ∧ (∃ r ∈ rP, mulN r.2 s ∈ pE) ∧
        mulN (tW uw'.2) s = mulN g (tW uw.2) := by
  have h := m22Check_parts.2.2.2.1
  simp only [schB, List.all_eq_true] at h
  intro uw huw g hg
  have h1 := h uw huw g hg
  cases hf : (((List.range 64).map fun b => orbL.filter fun p => p.1 % 64 == b).getD
      (mvN g uw.1 % 64) []).find? (fun p => p.1 == mvN g uw.1) with
  | none =>
    rw [hf] at h1
    exact absurd h1 Bool.false_ne_true
  | some uw' =>
    rw [hf] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, Std.HashSet.contains_ofList,
      List.contains_iff_mem, List.any_eq_true] at h1
    refine ⟨uw', mem_orbL_of_mem_getD (List.mem_of_find?_eq_some hf), ?_, _,
      by simp only [length_mulN, length_evalW], h1.1, h1.2⟩
    have := List.find?_some hf
    simpa using this

@[expose] def S0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 s0G

theorem s0B_spec :
    pG.length = 5 ∧ (∀ k < 5, pG.getD k [] = evalW 12 s0G (pS0W.getD k [])) ∧
      (∃ r ∈ rP, mulN r.2 one12 ∈ pE) ∧
      (∀ g ∈ s0G, ∀ r ∈ rP, ∃ r' ∈ rP, mulN r'.2 (mulN g r.1) ∈ pE) ∧
      (∀ r ∈ rP, mvN r.1 v0 = v0) ∧ ∀ p ∈ pE, mvN p v0 = v0 := by
  have h := m22Check_parts.2.2.1
  simp only [s0B, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, fun k hk => h2 k (List.mem_range.mpr hk), h3, h4, h5, h6⟩

theorem s0G_unit : ∀ g ∈ s0G, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨tU w, tU_val w⟩

theorem s0G_valid : ∀ g ∈ s0G, ValidN 12 g := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact validN_evalW gG validN_gG w

theorem exists_S0_of_evalW (w : List ℕ) :
    ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (evalW 12 s0G w) :=
  exists_evalW s0G s0G_valid s0G_unit w

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
    subB 12 pG pE = true ∧ pE.length = 256 ∧
      ∀ v < 4096, (∀ g ∈ pG, mvN g v = v) → v = 0 ∨ v = v0 := by
  have h := m22Check_parts.2.2.2.2.1
  simp only [pB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h4⟩ := h
  refine ⟨h1, h2, fun v hv hfix => ?_⟩
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

theorem pG_unit : ∀ g ∈ pG, ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hg
  have := s0B_spec.2.1 n (by rw [← s0B_spec.1]; exact hn)
  rw [List.getD_eq_getElem _ _ hn] at this
  rw [this]
  exact exists_S0_of_evalW _

theorem pG_unit' : ∀ g ∈ pG, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g :=
  fun g hg => let ⟨u, _, hu⟩ := pG_unit g hg; ⟨u, hu⟩

theorem PM_le_S0 : PM ≤ S0 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨v, hv, hv'⟩ := pG_unit _ hu
  have he : u = v := Units.ext (by rw [hv', decN_colsN])
  rw [he]
  exact hv

theorem mem_PM_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ PM ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ pE :=
  mem_genSubN_iff_of pB_spec.1 pG_unit' u

theorem card_PM : Nat.card PM = 256 := by
  rw [PM, card_genSubN_of pB_spec.1 pG_unit']
  exact pB_spec.2.1

theorem exists_mem_PM {c : List ℕ} (hc : c ∈ pE) :
    ∃ u ∈ PM, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c :=
  exists_mem_of_elemsOf pB_spec.1 pG_unit' hc

theorem rP_spec :
    (∀ r ∈ rP, (∃ w, r.1 = evalW 12 s0G w) ∧ mulN r.1 r.2 = one12) ∧
      (rP.length = 15 ∧
        ∀ i < 15, ∀ j < i, mulN (rP.getD j ([], [])).2 (rP.getD i ([], [])).1 ∉ pE) := by
  have h := m22Check_parts.2.2.2.2.2.2.2.1
  simp only [ovB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨-, h2a, h2b⟩, h3a, h3b⟩, -⟩, -⟩ := h
  have hlen : rP.length = 15 := by simpa using h3a
  refine ⟨fun r hr => ?_, hlen, fun i hi j hj => ?_⟩
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
    have h6 := h2a n (List.mem_range.mpr (by omega))
    rw [List.getD_eq_getElem _ _ hn] at h6
    simp only [beq_iff_eq] at h6
    have h7 := h2b _ (List.getElem_mem hn)
    simp only [beq_iff_eq] at h7
    exact ⟨⟨_, h6⟩, h7⟩
  · have := h3b i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
    simpa [Std.HashSet.contains_ofList] using this

theorem validN_rP : ∀ r ∈ rP, ValidN 12 r.1 ∧ ValidN 12 r.2 := by
  have h : ∀ r ∈ rP, validB 12 r.1 = true ∧ validB 12 r.2 = true := by decide
  intro r hr
  exact ⟨validB_iff.mp (h r hr).1, validB_iff.mp (h r hr).2⟩

theorem exists_S0_of_rP {r : List ℕ × List ℕ} (hr : r ∈ rP) :
    ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 r.1 := by
  obtain ⟨w, hw⟩ := (rP_spec.1 r hr).1
  rw [hw]
  exact exists_S0_of_evalW w

theorem rP_unit {r : List ℕ × List ℕ} (hr : r ∈ rP) :
    ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 r.1 ∧
      ((u⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 r.2 :=
  let ⟨u, hu, hu'⟩ := exists_S0_of_rP hr
  ⟨u, hu, hu', inv_val_of (validN_rP r hr).1 (validN_rP r hr).2 hu' (rP_spec.1 r hr).2⟩

theorem exists_rP_of_mem_S0 {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    ∃ r ∈ rP, mulN r.2 (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
  obtain ⟨-, -, ho, hg, -⟩ := s0B_spec
  have key : ∀ c ∈ rP, ∀ cu : GL (Fin 12) (ZMod 2),
      ((cu⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c.2 →
      ∀ y : GL (Fin 12) (ZMod 2),
        (cu⁻¹ * y ∈ PM ↔ mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) := by
    intro c hc cu hcu y
    rw [mem_PM_iff, Units.val_mul, colsN_mul, hcu, colsN_decN (validN_rP c hc).2]
  have hstep : ∀ t : GL (Fin 12) (ZMod 2),
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ s0G → ∀ y : GL (Fin 12) (ZMod 2),
        (∃ c ∈ rP, mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) →
        ∃ c ∈ rP, mulN c.2
          (colsN ((t * y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
    rintro t ht y ⟨c, hc, hcy⟩
    obtain ⟨c', hc', hc't⟩ := hg _ ht c hc
    obtain ⟨cu, -, hcu1, hcu2⟩ := rP_unit hc
    obtain ⟨cu', -, -, hcu'2⟩ := rP_unit hc'
    refine ⟨c', hc', (key c' hc' cu' hcu'2 _).mp ?_⟩
    have e : cu'⁻¹ * (t * y) = (cu'⁻¹ * (t * cu)) * (cu⁻¹ * y) := by group
    rw [e]
    refine PM.mul_mem ((key c' hc' cu' hcu'2 _).mpr ?_) ((key c hc cu hcu2 y).mpr hcy)
    rw [Units.val_mul, colsN_mul, hcu1, colsN_decN (validN_rP c hc).1]
    exact hc't
  have hpow : ∀ t : GL (Fin 12) (ZMod 2),
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ s0G → ∀ (m : ℕ) (y : GL (Fin 12) (ZMod 2)),
      (∃ c ∈ rP, mulN c.2 (colsN (y : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) →
      ∃ c ∈ rP, mulN c.2
        (colsN ((t ^ m * y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
    intro t ht m
    induction m with
    | zero =>
      intro y hy
      rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep t ht _ (ih y hy)
  unfold S0 genSubN at hs
  refine Subgroup.closure_induction_left (p := fun (u : GL (Fin 12) (ZMod 2)) _ =>
    ∃ c ∈ rP, mulN c.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE) ?_ ?_ ?_ hs
  · rw [Units.val_one, colsN_one]
    exact ho
  · intro t ht y _ hy
    exact hstep t ht y hy
  · intro t ht y _ hy
    have hfin : IsOfFinOrder t := isOfFinOrder_of_finite t
    have hinv : t⁻¹ = t ^ (orderOf t - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow t ht _ y hy

theorem mem_S0_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ S0 ↔ ∃ r ∈ rP, mulN r.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) ∈ pE := by
  refine ⟨exists_rP_of_mem_S0, fun ⟨r, hr, h⟩ => ?_⟩
  obtain ⟨ru, hru, -, hinv⟩ := rP_unit hr
  have hq : ru⁻¹ * u ∈ PM := by
    rw [mem_PM_iff, Units.val_mul, colsN_mul, hinv, colsN_decN (validN_rP r hr).2]
    exact h
  rw [← mul_inv_cancel_left ru u]
  exact S0.mul_mem hru (PM_le_S0 hq)

theorem exists_S0_of_coset {s : List ℕ} (hs : s.length = 12)
    (h : ∃ r ∈ rP, mulN r.2 s ∈ pE) :
    ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 s := by
  obtain ⟨r, hr, hq⟩ := h
  obtain ⟨ru, hru, hru1, hru2⟩ := rP_unit hr
  obtain ⟨qu, hqu, hqu'⟩ := exists_mem_PM hq
  refine ⟨ru * qu, S0.mul_mem hru (PM_le_S0 hqu), ?_⟩
  have hv := validN_rP r hr
  rw [Units.val_mul, hqu', decN_mulN hv.2.1 hs, ← Matrix.mul_assoc, ← hru2, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem card_S0 : Nat.card S0 = 3840 := by
  classical
  obtain ⟨hlen, hdis⟩ := rP_spec.2
  have hmem : ∀ k : Fin 15, rP.getD k ([], []) ∈ rP := fun k => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
    exact List.getElem_mem _
  let ru : Fin 15 → GL (Fin 12) (ZMod 2) := fun k => Classical.choose (rP_unit (hmem k))
  have hru : ∀ k, ru k ∈ S0 ∧
      (ru k : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (rP.getD k ([], [])).1 ∧
      (((ru k)⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        decN 12 (rP.getD k ([], [])).2 :=
    fun k => Classical.choose_spec (rP_unit (hmem k))
  have hcol : ∀ j k : Fin 15,
      colsN (((ru j)⁻¹ * ru k : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        mulN (rP.getD j ([], [])).2 (rP.getD k ([], [])).1 := by
    intro j k
    rw [Units.val_mul, colsN_mul, (hru j).2.2, (hru k).2.1,
      colsN_decN (validN_rP _ (hmem j)).2, colsN_decN (validN_rP _ (hmem k)).1]
  have hne : ∀ j k : Fin 15, (ru j)⁻¹ * ru k ∈ PM → j = k := by
    intro j k h
    by_contra hjk
    rcases lt_or_gt_of_ne (fun h' => hjk (Fin.ext h')) with hlt | hlt
    · have h3 := (mem_PM_iff _).mp h
      rw [hcol] at h3
      exact hdis k k.2 j hlt h3
    · have h' : (ru k)⁻¹ * ru j ∈ PM := by
        have := PM.inv_mem h
        rwa [mul_inv_rev, inv_inv] at this
      have h3 := (mem_PM_iff _).mp h'
      rw [hcol] at h3
      exact hdis j j.2 k hlt h3
  let f : Fin 15 × PM → S0 := fun x => ⟨ru x.1 * x.2, S0.mul_mem (hru x.1).1 (PM_le_S0 x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨j, p⟩ ⟨k, q⟩ h
    have h1 : ru j * p = ru k * q := congrArg Subtype.val h
    have h2 : (ru j)⁻¹ * ru k = (p : GL (Fin 12) (ZMod 2)) * (q : GL (Fin 12) (ZMod 2))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 : (ru j)⁻¹ * ru k ∈ PM := by
      rw [h2]
      exact PM.mul_mem p.2 (PM.inv_mem q.2)
    obtain rfl := hne j k h3
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h1))
  have hs : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨r, hr, hq⟩ := exists_rP_of_mem_S0 hs
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
    let k : Fin 15 := ⟨n, by rw [← hlen]; exact hn⟩
    have hk : rP.getD k ([], []) = rP[n] := List.getD_eq_getElem _ _ hn
    have hp : (ru k)⁻¹ * s ∈ PM := by
      rw [mem_PM_iff, Units.val_mul, colsN_mul, (hru k).2.2, hk,
        colsN_decN (validN_rP _ hr).2]
      exact hq
    exact ⟨(k, ⟨_, hp⟩), Subtype.ext (mul_inv_cancel_left _ _)⟩
  rw [← Nat.card_eq_of_bijective f ⟨hf, hs⟩, Nat.card_prod, card_PM, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem S0_le : S0 ≤ m22 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨w, -, hw⟩ := List.mem_map.mp (show colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈
    s0G from hu)
  have : u = tU w := by
    apply Units.ext
    rw [tU_val, hw, decN_colsN]
  rw [this]
  exact tU_mem w

theorem S0_fix {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    (s : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0 := by
  obtain ⟨r, hr, hq⟩ := exists_rP_of_mem_S0 hs
  obtain ⟨ru, -, hru1, hru2⟩ := rP_unit hr
  have he : colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      mulN r.1 (mulN r.2 (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)))) := by
    calc colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))
        = colsN ((ru * (ru⁻¹ * s) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
          rw [mul_inv_cancel_left]
      _ = _ := by
          rw [Units.val_mul, colsN_mul, Units.val_mul, colsN_mul, hru1, hru2,
            colsN_decN (validN_rP r hr).1, colsN_decN (validN_rP r hr).2]
  rw [mulVec_vecN, he, mvN_mulN, s0B_spec.2.2.2.2.2 _ hq, s0B_spec.2.2.2.2.1 r hr]

theorem tU_mulVec {uw : ℕ × List ℕ} (huw : uw ∈ orbL) :
    ((tU uw.2 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = vecN 12 uw.1 := by
  rw [tU_val, decN_mulVec (length_evalW gG _), orbB_spec.2.2.2 uw huw]

theorem decomp {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ m22) :
    ∃ uw ∈ orbL, ∃ s ∈ S0, x = tU uw.2 * s := by
  have hstep : ∀ i < 2, ∀ y : GL (Fin 12) (ZMod 2), (∃ uw ∈ orbL, ∃ s ∈ S0, y = tU uw.2 * s) →
      ∃ uw ∈ orbL, ∃ s ∈ S0, gU i * y = tU uw.2 * s := by
    rintro i hi y ⟨uw, huw, s, hs, rfl⟩
    have hg : gG.getD i one12 ∈ gG := by
      rw [List.getD_eq_getElem _ _ (by simp [gG]; omega)]
      exact List.getElem_mem _
    obtain ⟨uw', huw', -, σ, hσlen, hσ, hσeq⟩ := schB_spec uw huw _ hg
    obtain ⟨σU, hσU, hσU'⟩ := exists_S0_of_coset hσlen hσ
    refine ⟨uw', huw', σU * s, S0.mul_mem hσU hs, ?_⟩
    have key : gU i * tU uw.2 = tU uw'.2 * σU := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, gU_val, tU_val, tU_val, hσU',
        ← decN_mulN (validN_getD validN_gG i).1 (length_evalW gG _),
        ← decN_mulN (length_evalW gG _) hσlen, hσeq]
    rw [← mul_assoc, key, mul_assoc]
  have hpow : ∀ i < 2, ∀ m : ℕ, ∀ y : GL (Fin 12) (ZMod 2),
      (∃ uw ∈ orbL, ∃ s ∈ S0, y = tU uw.2 * s) →
      ∃ uw ∈ orbL, ∃ s ∈ S0, gU i ^ m * y = tU uw.2 * s := by
    intro i hi m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep i hi _ (ih y hy)
  have hgen : ∀ x ∈ ({m22a, m22b} : Set (GL (Fin 12) (ZMod 2))), ∃ i < 2, x = gU i := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, by norm_num, by simp [gU]⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨1, by norm_num, by simp [gU, hx]⟩
  refine Subgroup.closure_induction_left
    (p := fun x _ => ∃ uw ∈ orbL, ∃ s ∈ S0, x = tU uw.2 * s) ?_ ?_ ?_ hx
  · exact ⟨_, v0_mem, 1, one_mem _, by simp [tU]⟩
  · intro x hx y _ hy
    obtain ⟨i, hi, rfl⟩ := hgen x hx
    exact hstep i hi y hy
  · intro x hx y _ hy
    obtain ⟨i, hi, rfl⟩ := hgen x hx
    have hfin : IsOfFinOrder (gU i) := isOfFinOrder_of_finite _
    have hinv : (gU i)⁻¹ = gU i ^ (orderOf (gU i) - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow i hi _ y hy

theorem mulVec_decomp {uw : ℕ × List ℕ} (huw : uw ∈ orbL)
    {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    ((tU uw.2 * s : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = vecN 12 uw.1 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, S0_fix hs, tU_mulVec huw]

theorem mem_S0_of_fix {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ m22)
    (hfix : (x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0) :
    x ∈ S0 := by
  obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hx
  have h1 := mulVec_decomp huw hs
  rw [hfix] at h1
  have hu : uw.1 = v0 := (vecN_inj (by decide) (orbL_lt huw) h1).symm
  have he : uw = (v0, []) := orbL_ext huw v0_mem hu
  rw [he]
  simpa [tU] using hs

theorem card_m22 : Nat.card m22 = 2661120 := by
  let f : {uw // uw ∈ orbL} × S0 → m22 := fun p =>
    ⟨tU p.1.1.2 * p.2, m22.mul_mem (tU_mem _) (S0_le p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · have h1 : tU p.1.1.2 * p.2 = tU q.1.1.2 * q.2 := congrArg Subtype.val h
      have h2 := mulVec_decomp p.1.2 p.2.2
      rw [h1, mulVec_decomp q.1.2 q.2.2] at h2
      have hpq : p.1 = q.1 := Subtype.ext (orbL_ext p.1.2 q.1.2
        (vecN_inj (orbL_lt p.1.2) (orbL_lt q.1.2) h2.symm))
      rw [hpq] at h1
      exact Prod.ext hpq (Subtype.ext (mul_left_cancel h1))
    · obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hx
      exact ⟨(⟨uw, huw⟩, ⟨s, hs⟩), rfl⟩
  have hnd : orbL.Nodup := List.Nodup.of_map _ orbB_spec.2.2.1
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, card_S0,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := orbL) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, orbB_spec.2.1]

end CFSG.Quasithin.H13.M22Cert
