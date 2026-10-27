module

public import CFSG.Quasithin.H13.L32NO3Model
public import CFSG.Quasithin.H13.L32NG5Model
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.H13.O3Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert

theorem xor_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [h256] at ha hb ⊢
  exact Nat.xor_lt_two_pow ha hb

theorem exists_small_image {x : GL (Fin 8) (ZMod 2)}
    (h : smallImgB (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true) :
    ∃ F : Finset (Fin 8 → ZMod 2), F.card ≤ 4 ∧
      ∀ v, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v ∈ F := by
  classical
  simp only [smallImgB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨(spanN (imgBasis (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))))).toFinset.image vec8,
    (Finset.card_image_le).trans ((List.toFinset_card_le _).trans h1), fun v => ?_⟩
  rw [← vec8_code8 v, mulVec_vec8, ← vec8_xor]
  exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr (h2 _ (List.mem_range.mpr
    (code8_lt v))))

theorem full_image {x : GL (Fin 8) (ZMod 2)}
    (h : fullImgB (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true) :
    (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v).card = 16 ∧
    (∀ u, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec u = u →
      ∃ v, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v = u) ∧
    ∀ v, quadOf q3 ((x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v) = 0 := by
  classical
  set c := colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) with hc
  set S := spanN (imgBasis c) with hS
  simp only [fullImgB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨hlen, hsort⟩, hlt⟩, himg⟩, hsur⟩, hfix⟩, hsing⟩ := h
  have hnd : S.Nodup := by
    have h2 : (S.mergeSort).Nodup :=
      (List.isChain_iff_pairwise.mp hsort).imp (fun hab => ne_of_lt hab)
    exact (List.mergeSort_perm _ _).nodup_iff.mp h2
  have hval : ∀ v : Fin 8 → ZMod 2, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v =
      vec8 (mv8 c (code8 v) ^^^ code8 v) := fun v => by
    rw [vec8_xor, ← mulVec_vec8, vec8_code8]
  refine ⟨?_, fun u hu => ?_, fun v => ?_⟩
  · have himage : (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
        (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v) = S.toFinset.image vec8 := by
      ext u
      simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨_, himg _ (List.mem_range.mpr (code8_lt v)), (hval v).symm⟩
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨n, hn, hns⟩ := hsur s hs
        refine ⟨vec8 n, ?_⟩
        rw [hval, code8_vec8 (List.mem_range.mp hn), hns]
    rw [himage, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
    intro a ha b hb hab
    exact vec8_inj (hlt a (List.mem_toFinset.mp ha)) (hlt b (List.mem_toFinset.mp hb)) hab
  · have hcu : mv8 c (code8 u) = code8 u := by
      have : vec8 (mv8 c (code8 u)) = vec8 (code8 u) := by
        rw [← mulVec_vec8, vec8_code8, hu]
      exact vec8_inj (mv8_lt (valid8_colsOf _) _) (code8_lt u) this
    rcases hfix (code8 u) (List.mem_range.mpr (code8_lt u)) with h' | h'
    · exact absurd hcu h'
    · obtain ⟨n, hn, hns⟩ := hsur _ h'
      refine ⟨vec8 n, ?_⟩
      rw [hval, code8_vec8 (List.mem_range.mp hn), hns, vec8_code8]
  · rw [hval, q3_eq, ← quadN_spec]
    have := hsing _ (himg _ (List.mem_range.mpr (code8_lt v)))
    rw [this]
    rfl

theorem h1_small {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ H1)
    (hxF : x ∉ omega3F) (hxx : x * x = 1) :
    ∃ F : Finset (Fin 8 → ZMod 2), F.card ≤ 4 ∧
      ∀ v, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v ∈ F := by
  have h := o3Check_parts.2.1
  simp only [h1B, List.all_eq_true, Bool.or_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  rcases h _ ((mem_H1_iff x).mp hx) with (h1 | h1) | h1
  · exact absurd ((mem_omega3F_iff x).mpr h1) hxF
  · exfalso
    apply h1
    rw [← colsOf_mul, ← Units.val_mul, hxx, Units.val_one, colsOf_one]
  · exact exists_small_image h1

@[expose] def gam (c : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := if c = 0 then H2 else omega3N

theorem mem_gam_iff {c : ℕ} (hc : c < 2)
    (u : GL (Fin 8) (ZMod 2)) :
    u ∈ gam c ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gamE c := by
  interval_cases c
  · exact mem_H2_iff u
  · exact mem_omega3N_iff u

theorem card_gam {c : ℕ} (hc : c < 2) :
    Nat.card (gam c) = pOrd c * 225 := by
  interval_cases c
  · exact card_H2
  · exact card_omega3N

theorem omega3_le_gam {c : ℕ} (hc : c < 2) : omega3 ≤ gam c := by
  interval_cases c
  · exact omega3_le_H2
  · exact omega3_le_omega3F.trans omega3F_le_omega3N

theorem gam_le_omega3N {c : ℕ} (hc : c < 2) :
    gam c ≤ omega3N := by
  interval_cases c
  · exact H2_le_omega3N
  · exact le_rfl

theorem gamE_mem_omNE {c : ℕ} (hc : c < 2) {x : List ℕ}
    (hx : x ∈ gamE c) : x ∈ omNE := by
  interval_cases c
  · obtain ⟨w, rfl⟩ := mem_elemsOf hx
    obtain ⟨u, hu, hu'⟩ := exists_evalW _ (subB_spec basic_spec.2.2.2.2.1.1).2.2.2.2
      (unit_of_omNE h2G_mem) w
    rw [← colsOf_dec8 (valid8_evalW _ (subB_spec basic_spec.2.2.2.2.1.1).2.2.2.2 w), ← hu']
    exact colsOf_mem_omNE (H2_le_omega3N hu)
  · exact hx

theorem exists_mem_gam {c : ℕ} (hc : c < 2) {x : List ℕ}
    (hx : x ∈ gamE c) : ∃ u ∈ gam c, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x := by
  obtain ⟨u, -, hu⟩ := exists_mem_omega3N (gamE_mem_omNE hc hx)
  refine ⟨u, (mem_gam_iff hc u).mpr ?_, hu⟩
  rw [hu, colsOf_dec8 ((subB_spec basic_spec.2.2.1.1).1 _ (gamE_mem_omNE hc hx))]
  exact hx

@[expose] def PP (c : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (pG c)

theorem mem_zero_one {c : ℕ} (hc : c < 2) : c ∈ [0, 1] := by
  interval_cases c <;> simp

theorem pB_spec {c : ℕ} (hc : c < 2) :
    subB (pG c) (pE c) = true ∧ (pE c).length = pOrd c ∧ (∀ g ∈ pG c, g ∈ gamE c) ∧
      ∀ v < 256, (∀ g ∈ pG c, mv8 g v = v) → v = 0 ∨ v = vS c := by
  have h := (o3Check_parts.2.2 c (mem_zero_one hc)).1
  simp only [pB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun v hv hfix => ?_⟩
  have := h4 v (List.mem_range.mpr hv)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  rcases this with (h5 | h5) | h5
  · exfalso
    have h6 : ((pG c).all fun g => mv8 g v == v) = true := by
      simp only [List.all_eq_true, beq_iff_eq]
      exact hfix
    rw [h6] at h5
    exact Bool.noConfusion h5
  · exact Or.inl h5
  · exact Or.inr h5

theorem unit_of_gamE {c : ℕ} (hc : c < 2) {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ gamE c) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_gam hc (h g hg); ⟨u, hu⟩

theorem genSub_le_gam {c : ℕ} (hc : c < 2) {gens : List (List ℕ)}
    (h : ∀ g ∈ gens, g ∈ gamE c) : genSub gens ≤ gam c :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_gam_iff hc u).mpr (h _ hu)

theorem PP_le_gam {c : ℕ} (hc : c < 2) : PP c ≤ gam c :=
  genSub_le_gam hc (pB_spec hc).2.2.1

theorem mem_PP_iff {c : ℕ} (hc : c < 2) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ PP c ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ pE c :=
  mem_genSub_iff_of (pB_spec hc).1 (unit_of_gamE hc (pB_spec hc).2.2.1) u

theorem card_PP {c : ℕ} (hc : c < 2) : Nat.card (PP c) = pOrd c := by
  rw [PP, card_genSub_of (pB_spec hc).1 (unit_of_gamE hc (pB_spec hc).2.2.1)]
  exact (pB_spec hc).2.1

theorem exists_mem_PP {c : ℕ} (hc : c < 2) {x : List ℕ}
    (hx : x ∈ pE c) : ∃ u ∈ PP c, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hx
  exact exists_evalW _ (subB_spec (pB_spec hc).1).2.2.2.2 (unit_of_gamE hc (pB_spec hc).2.2.1) w

theorem eq_of_fixed_PP {c : ℕ} (hc : c < 2) (v : Fin 8 → ZMod 2)
    (hv : ∀ g ∈ PP c, (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = vec8 (vS c) := by
  have hval := (subB_spec (pB_spec hc).1).2.2.2.2
  have hfix : ∀ p ∈ pG c, mv8 p (code8 v) = code8 v := by
    intro p hp
    obtain ⟨u, hu⟩ := unit_of_gamE hc (pB_spec hc).2.2.1 p hp
    have := hv u (mem_genSub_of_mem hval hp hu)
    rw [← vec8_code8 v, hu, dec8_mulVec] at this
    exact vec8_inj (mv8_lt (hval p hp) _) (code8_lt v) (by rw [this, vec8_code8])
  rcases (pB_spec hc).2.2.2 (code8 v) (code8_lt v) hfix with h | h
  · left
    rw [← vec8_code8 v, h, vec8_zero]
  · right
    rw [← vec8_code8 v, h]

theorem pG_fix {c : ℕ} (hc : c < 2) : ∀ g ∈ pG c, mv8 g (vS c) = vS c := by
  interval_cases c <;> decide

theorem PP_fix {c : ℕ} (hc : c < 2) {p : GL (Fin 8) (ZMod 2)} (hp : p ∈ PP c) :
    (p : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) = vec8 (vS c) := by
  unfold PP genSub at hp
  refine Subgroup.closure_induction (p := fun (p : GL (Fin 8) (ZMod 2)) _ =>
    (p : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) = vec8 (vS c)) ?_ ?_ ?_ ?_ hp
  · intro g hg
    rw [mulVec_vec8, pG_fix hc _ hg]
  · simp
  · intro x y _ _ hx hy
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy, hx]
  · intro x _ hx
    calc ((x⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c))
        = ((x⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
            ((x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c))) := by rw [hx]
      _ = vec8 (vS c) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]

@[expose] def WW (c : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (cxs c (xsS c) ++ [xsS c])

theorem wB_spec {c : ℕ} (hc : c < 2) :
    xsS c ∈ pE c ∧ subB (cxs c (xsS c) ++ [xsS c]) (wE c) = true ∧ (wE c).length = 8 ∧
    (∀ x ∈ pE c, x ∈ om3FE ∨ mul8 x x ≠ one8 ∨ smallImgB x = true ∨ x ∈ wE c) ∧
    ∀ w ∈ wE c, (w ∈ om3E ∧ mv8 w (vS c) = vS c ∧ mv8 w (wS c).1 = (wS c).1) ∨
      (w ∉ om3FE ∧ fullImgB w = true ∧ subB (cxs c w ++ [w]) (elemsOf (cxs c w ++ [w])) = true ∧
        (elemsOf (cxs c w ++ [w])).length = 8 ∧ ∀ e ∈ elemsOf (cxs c w ++ [w]), e ∈ wE c) := by
  have h := (o3Check_parts.2.2 c (mem_zero_one hc)).2.1
  simp only [wB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨List.contains_iff_mem.mp h0, h1, h2, fun x hx => ?_, fun w hw => ?_⟩
  · rcases h3 x hx with ((h | h) | h) | h
    · exact Or.inl (List.contains_iff_mem.mp h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (List.contains_iff_mem.mp h)))
  · rcases h4 w hw with ⟨⟨a, b⟩, d⟩ | ⟨⟨a, b⟩, ⟨d, e⟩, f⟩
    · exact Or.inl ⟨List.contains_iff_mem.mp a, b, d⟩
    · refine Or.inr ⟨fun h => ?_, b, d, e, fun x hx => List.contains_iff_mem.mp (f x hx)⟩
      rw [List.contains_iff_mem.mpr h] at a
      exact Bool.noConfusion a

theorem mem_cxs_iff {c : ℕ} (hc : c < 2) {x : GL (Fin 8) (ZMod 2)}
    (y : GL (Fin 8) (ZMod 2)) :
    colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈
        cxs c (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) ↔
      y ∈ PP c ⊓ omega3 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2))) := by
  simp only [cxs, List.mem_filter, Bool.and_eq_true, beq_iff_eq, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    ← mem_PP_iff hc, ← mem_omega3_iff]
  constructor
  · rintro ⟨hP, h3, hcomm⟩
    refine ⟨⟨hP, h3⟩, eq_of_colsOf_eq ?_⟩
    rw [Units.val_mul, colsOf_mul, Units.val_mul, colsOf_mul]
    exact hcomm
  · rintro ⟨⟨hP, h3⟩, hcomm⟩
    refine ⟨hP, h3, ?_⟩
    rw [← colsOf_mul, ← colsOf_mul, ← Units.val_mul, ← Units.val_mul, hcomm]

theorem genSub_cxs {c : ℕ} (hc : c < 2) (x : GL (Fin 8) (ZMod 2)) :
    genSub (cxs c (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) ++
      [colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))]) =
    (PP c ⊓ omega3 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2)))) ⊔
      Subgroup.zpowers x := by
  unfold genSub
  rw [← Subgroup.closure_eq
    (PP c ⊓ omega3 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2)))),
    Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_singleton, Set.mem_union,
    SetLike.mem_coe, Set.mem_singleton_iff, mem_cxs_iff hc]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (eq_of_colsOf_eq h)
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl

theorem cxs_sub {c : ℕ} {x : List ℕ} : ∀ y ∈ cxs c x, y ∈ pE c := fun _ hy =>
  (List.mem_filter.mp hy).1

theorem wG_unit {c : ℕ} (hc : c < 2) :
    ∀ g ∈ cxs c (xsS c) ++ [xsS c], ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨u, -, hu⟩ := exists_mem_PP hc (cxs_sub _ hg)
    exact ⟨u, hu⟩
  · rw [List.mem_singleton.mp hg]
    obtain ⟨u, -, hu⟩ := exists_mem_PP hc (wB_spec hc).1
    exact ⟨u, hu⟩

theorem mem_WW_iff {c : ℕ} (hc : c < 2) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ WW c ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ wE c :=
  mem_genSub_iff_of (wB_spec hc).2.1 (wG_unit hc) u

theorem card_WW {c : ℕ} (hc : c < 2) : Nat.card (WW c) = 8 := by
  rw [WW, card_genSub_of (wB_spec hc).2.1 (wG_unit hc)]
  exact (wB_spec hc).2.2.1

theorem mem_WW {c : ℕ} (hc : c < 2) {w : GL (Fin 8) (ZMod 2)}
    (hw : w ∈ WW c) :
    (w ∈ omega3 ∧ (w : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)) = vec8 (vS c) ∧
      (w : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (wS c).1) = vec8 (wS c).1) ∨
    (w ∉ omega3F ∧ fullImgB (colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true) := by
  rcases (wB_spec hc).2.2.2.2 _ ((mem_WW_iff hc w).mp hw) with ⟨h1, h2, h3⟩ | ⟨h1, h2, -⟩
  · exact Or.inl ⟨(mem_omega3_iff w).mpr h1, by rw [mulVec_vec8, h2], by rw [mulVec_vec8, h3]⟩
  · exact Or.inr ⟨fun h => h1 ((mem_omega3F_iff w).mp h), h2⟩

theorem eq_WW_of {c : ℕ} (hc : c < 2) {x : GL (Fin 8) (ZMod 2)}
    (hxP : x ∈ PP c) (hxF : x ∉ omega3F) (hxx : x * x = 1)
    (hbig : ∀ F : Finset (Fin 8 → ZMod 2), F.card ≤ 4 →
      ∃ v, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v ∉ F) :
    (PP c ⊓ omega3 ⊓ Subgroup.centralizer ({x} : Set (GL (Fin 8) (ZMod 2)))) ⊔
      Subgroup.zpowers x = WW c := by
  have hxW : colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ wE c := by
    rcases (wB_spec hc).2.2.2.1 _ ((mem_PP_iff hc x).mp hxP) with h | h | h | h
    · exact absurd ((mem_omega3F_iff x).mpr h) hxF
    · exfalso
      apply h
      rw [← colsOf_mul, ← Units.val_mul, hxx, Units.val_one, colsOf_one]
    · exfalso
      obtain ⟨F, hF, hFx⟩ := exists_small_image h
      obtain ⟨v, hv⟩ := hbig F hF
      exact hv (hFx v)
    · exact h
  rcases (wB_spec hc).2.2.2.2 _ hxW with ⟨h1, -⟩ | ⟨-, -, hsub, hlen, hE⟩
  · exact absurd (omega3_le_omega3F ((mem_omega3_iff x).mpr h1)) hxF
  · rw [← genSub_cxs hc]
    have hunit : ∀ g ∈ cxs c (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) ++
        [colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))], ∃ u : GL (Fin 8) (ZMod 2),
          (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨u, -, hu⟩ := exists_mem_PP hc (cxs_sub _ hg)
        exact ⟨u, hu⟩
      · exact ⟨x, by rw [List.mem_singleton.mp hg, dec8_colsOf]⟩
    have hle : genSub (cxs c (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) ++
        [colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))]) ≤ WW c := fun u hu =>
      (mem_WW_iff hc u).mpr (hE _ ((mem_genSub_iff_of hsub hunit u).mp hu))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_WW hc, card_genSub_of hsub hunit, hlen]

theorem inv_spec {c : ℕ} (hc : c < 2) {x : GL (Fin 8) (ZMod 2)}
    (hx : x ∈ gam c) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    ∃ w : Fin 8 → ZMod 2, b5V w (vec8 (vS c)) = 0 ∧
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w ≠ 0 ∧
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w ≠ vec8 (vS c) := by
  have h := (o3Check_parts.2.2 c (mem_zero_one hc)).2.2.1
  simp only [invB, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, List.any_eq_true, Bool.and_eq_true] at h
  have hvlt : vS c < 256 := by interval_cases c <;> decide
  rcases h _ ((mem_gam_iff hc x).mp hx) with (h1 | h1) | ⟨n, hn, hb, hnot⟩
  · exact absurd (eq_of_colsOf_eq (by rw [h1, Units.val_one, colsOf_one])) hx1
  · exfalso
    apply h1
    rw [← colsOf_mul, ← Units.val_mul, hxx, Units.val_one, colsOf_one]
  · refine ⟨vec8 n, ?_, ?_, ?_⟩
    · rw [← b5N_spec, hb]
      rfl
    · intro h0
      have : mv8 (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) n ^^^ n = 0 := by
        apply vec8_inj (xor_lt_256 (mv8_lt (valid8_colsOf _) n) (List.mem_range.mp hn))
          (by norm_num)
        rw [vec8_xor, ← mulVec_vec8, h0, vec8_zero]
      rw [this] at hnot
      simp at hnot
    · intro h0
      have : mv8 (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) n ^^^ n = vS c := by
        apply vec8_inj (xor_lt_256 (mv8_lt (valid8_colsOf _) n) (List.mem_range.mp hn)) hvlt
        rw [vec8_xor, ← mulVec_vec8, h0]
      rw [this] at hnot
      simp at hnot

end CFSG.Quasithin.H13.O3Cert
