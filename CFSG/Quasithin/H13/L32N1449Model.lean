module

public import Certificates.Certificate7201
public import CFSG.Quasithin.H13.L32NO3Model3

public section

namespace CFSG.Quasithin.H13.Q1449Cert

open Mat8Cert L1442M S7Cert S8Cert G5Cert O3Cert

theorem q1449Check_eq : q1449Check = true :=
  Certificates.certificate7201

theorem q1449Check_parts :
    xsB = true ∧ cPWB = true ∧ alt0B = true ∧ expB = true ∧ cjB = true ∧ x0AB = true ∧
      betaB = true ∧ sigB = true ∧ irrB = true ∧ invRkB = true := by
  have h := q1449Check_eq
  simp only [q1449Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

@[expose] def fV (j : Fin 5) : Fin 5 → ZMod 2 := fun i => if i = j then 0 else 1

theorem fV_injective : Function.Injective fV := by decide

theorem vecN_fL (j : Fin 5) : MatNCert.vecN 5 (fL.getD j 0) = fV j := by
  fin_cases j <;> decide

theorem fV_perm (σ : Equiv.Perm (Fin 5)) (j : Fin 5) :
    (fun i => fV j (σ⁻¹ i)) = fV (σ j) := by
  funext i
  simp only [fV, Equiv.Perm.inv_eq_iff_eq]

theorem eq_sum_fV : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 →
    x = ∑ j ∈ Finset.univ.filter (fun j => x j = 1), fV j := by
  decide

theorem idxOf_fL : ∀ j < 5, fL.idxOf (fL.getD j 0) = j := by decide

theorem mem_fL {x : ℕ} (hx : x ∈ fL) : ∃ k : Fin 5, fL.getD k 0 = x := by
  simp only [fL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

@[expose] noncomputable def betaL (c : ℕ) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE (by norm_num))).comp
    (Matrix.mulVecLin (dec8 (betaC c)))

theorem betaL_vec8 (c n : ℕ) : betaL c (vec8 n) = MatNCert.vecN 5 (mv8 (betaC c) n) := by
  funext i
  simp only [betaL, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply,
    Matrix.mulVecLin_apply, dec8_mulVec]
  rfl

@[expose] def permL (σ : Equiv.Perm (Fin 5)) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (σ⁻¹ : Equiv.Perm (Fin 5))

theorem permL_apply (σ : Equiv.Perm (Fin 5)) (x : Fin 5 → ZMod 2) :
    permL σ x = fun i => x (σ⁻¹ i) := rfl

theorem permL_fV (σ : Equiv.Perm (Fin 5)) (j : Fin 5) : permL σ (fV j) = fV (σ j) :=
  fV_perm σ j

theorem permL_mul (σ τ : Equiv.Perm (Fin 5)) (x : Fin 5 → ZMod 2) :
    permL (σ * τ) x = permL σ (permL τ x) := by
  funext i
  simp [permL_apply, mul_inv_rev]

section Cert

variable {c : ℕ}

theorem xsB_spec (hc : c < 2) :
    xsS c ∈ wE c ∧ xsS c ∉ om3FE ∧ mul8 (xsS c) (xsS c) = one8 := by
  have h := q1449Check_parts.1
  simp only [xsB, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h c (mem_zero_one hc)
  refine ⟨List.contains_iff_mem.mp h1, fun h' => ?_, h3⟩
  rw [List.contains_iff_mem.mpr h'] at h2
  exact Bool.noConfusion h2

theorem exists_x0 (hc : c < 2) : ∃ x₀ : GL (Fin 8) (ZMod 2),
    colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c ∧ x₀ ∈ WW c ∧ x₀ ∉ omega3F := by
  obtain ⟨h1, h2, -⟩ := xsB_spec hc
  obtain ⟨u, hu⟩ := wG_unit hc (xsS c) (List.mem_append_right _ (List.mem_singleton_self _))
  have hcols : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c := by
    rw [hu, colsOf_dec8 ((subB_spec (wB_spec hc).2.1).1 _ h1)]
  refine ⟨u, hcols, (mem_WW_iff hc u).mpr (by rw [hcols]; exact h1), fun hF => h2 ?_⟩
  rw [← hcols]
  exact (mem_omega3F_iff u).mp hF

variable {x₀ : GL (Fin 8) (ZMod 2)}

theorem x0_mem (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    x₀ ∈ WW c ∧ x₀ ∉ omega3F := by
  obtain ⟨x₁, h1, hW, hF⟩ := exists_x0 hc
  have : x₀ = x₁ := eq_of_colsOf_eq (hx₀.trans h1.symm)
  subst this
  exact ⟨hW, hF⟩

theorem x0_not_mem_omega3 (hc : c < 2)
    (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) : x₀ ∉ omega3 :=
  fun h => (x0_mem hc hx₀).2 (omega3_le_omega3F h)

theorem x0_sq (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    x₀ * x₀ = 1 := by
  apply eq_of_colsOf_eq
  rw [Units.val_mul, colsOf_mul, hx₀, (xsB_spec hc).2.2, Units.val_one, colsOf_one]

theorem x0_full (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    fullImgB (colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true := by
  rcases mem_WW hc (x0_mem hc hx₀).1 with ⟨h3, -⟩ | ⟨-, hfull⟩
  · exact absurd h3 (x0_not_mem_omega3 hc hx₀)
  · exact hfull

theorem mem_WW_of_comm (hc : c < 2) {p : GL (Fin 8) (ZMod 2)} (hp : p ∈ PP c)
    (hcomm : ∀ w ∈ WW c, p * w = w * p) : p ∈ WW c := by
  have h := q1449Check_parts.2.1
  simp only [cPWB, List.all_eq_true, Bool.or_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true', List.all_eq_false, beq_iff_eq] at h
  rcases h c (mem_zero_one hc) _ ((mem_PP_iff hc p).mp hp) with h1 | ⟨w, hw, hne⟩
  · exact (mem_WW_iff hc p).mpr h1
  · exfalso
    apply hne
    obtain ⟨u, hu⟩ := wG_unit hc w hw
    have huW : u ∈ WW c := Subgroup.subset_closure (by
      show colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ cxs c (xsS c) ++ [xsS c]
      rw [hu, colsOf_dec8 ((subB_spec (wB_spec hc).2.1).2.2.2.2 _ hw)]
      exact hw)
    have h2 := hcomm u huW
    have h3 : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = w := by
      rw [hu, colsOf_dec8 ((subB_spec (wB_spec hc).2.1).2.2.2.2 _ hw)]
    rw [← h3, ← colsOf_mul, ← colsOf_mul, ← Units.val_mul, ← Units.val_mul, h2]

theorem x0_fix_iff (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (v : Fin 8 → ZMod 2) :
    (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v ↔
      ∃ w, (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w = v := by
  refine ⟨(full_image (x0_full hc hx₀)).2.1 v, ?_⟩
  rintro ⟨w, rfl⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Units.val_mul, x0_sq hc hx₀, Units.val_one,
    Matrix.one_mulVec, add_comm]

theorem x0_alt (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (v : Fin 8 → ZMod 2) :
    G5Cert.b5V ((x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) v = 0 := by
  have h := q1449Check_parts.2.2.1
  simp only [alt0B, List.all_eq_true, Bool.not_eq_true', List.mem_range] at h
  have h1 := h c (mem_zero_one hc) (code8 v) (code8_lt v)
  rw [← vec8_code8 v, mulVec_vec8, hx₀, ← b5N_spec, h1]
  rfl

theorem cen_pow (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ gam c) (hxc : x * x₀ = x₀ * x) : x ^ 240 = 1 := by
  have h := q1449Check_parts.2.2.2.1
  simp only [expB, List.all_eq_true, List.mem_filter, beq_iff_eq, and_imp] at h
  refine eq_one_of_colsOf ?_
  rw [colsOf_pow]
  refine h c (mem_zero_one hc) _ ((mem_gam_iff hc x).mp hx) ?_
  rw [← hx₀, ← colsOf_mul, ← colsOf_mul, ← Units.val_mul, ← Units.val_mul, hxc]

theorem mem_span_iff (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (v : Fin 8 → ZMod 2) :
    code8 v ∈ spanN (imgBasis (xsS c)) ↔ (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v := by
  have h := x0_full hc hx₀
  rw [hx₀] at h
  simp only [fullImgB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, himg⟩, hsur⟩, -⟩, -⟩ := h
  rw [x0_fix_iff hc hx₀]
  constructor
  · intro hv
    obtain ⟨n, hn, hns⟩ := hsur _ hv
    refine ⟨vec8 n, ?_⟩
    rw [mulVec_vec8, hx₀, ← vec8_xor, hns, vec8_code8]
  · rintro ⟨w, rfl⟩
    have h1 := himg (code8 w) (List.mem_range.mpr (code8_lt w))
    have h2 : mv8 (xsS c) (code8 w) ^^^ code8 w =
        code8 ((x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w) := by
      rw [← code8_vec8 (O3Cert.xor_lt_256 (mv8_lt ((subB_spec (wB_spec hc).2.1).1 _
        (xsB_spec hc).1) _) (code8_lt w)), vec8_xor, ← hx₀, ← mulVec_vec8, vec8_code8]
    rwa [h2] at h1

theorem exists_conj_x0 (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    {w : GL (Fin 8) (ZMod 2)} (hw : w ∈ WW c) (hw3 : w ∉ omega3) :
    ∃ h ∈ gam c, h * w * h⁻¹ = x₀ := by
  have h := q1449Check_parts.2.2.2.2.1
  simp only [cjB, List.all_eq_true, Bool.or_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h c (mem_zero_one hc) _ ((mem_WW_iff hc w).mp hw) with h3 | ⟨t, -, ⟨⟨ht1, ht2⟩, ht3⟩, ht4⟩
  · exact absurd ((mem_omega3_iff w).mpr h3) hw3
  · obtain ⟨k, hk, hk'⟩ := exists_cols_gam hc ht2
    refine ⟨k, hk, ?_⟩
    have hlen : t.2.2.length = 8 := by rw [← length_mul8 t.2.1 t.2.2, ht3]; rfl
    have hinv : dec8 t.2.2 = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      have h1 : (k : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 t.2.2 = 1 := by
        rw [← dec8_colsOf (k : Matrix (Fin 8) (Fin 8) (ZMod 2)), hk', ← dec8_mul8 _ _ hlen, ht3,
          dec8_one8]
      calc dec8 t.2.2 = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
            ((k : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 t.2.2) := by
            rw [Units.inv_mul_cancel_left]
        _ = _ := by rw [h1, mul_one]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← hinv, ← dec8_colsOf (k : Matrix (Fin 8) (Fin 8) (ZMod 2)),
      hk', ← dec8_colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2)),
      ← dec8_mul8 _ _ (valid8_colsOf _).1, ← dec8_mul8 _ _ hlen, ht4, ← hx₀,
      dec8_colsOf]

theorem xsS_not_mem_om3E (hc : c < 2) : xsS c ∉ om3E := by
  obtain ⟨x₁, h1, -, hF⟩ := exists_x0 hc
  intro h
  rw [← h1] at h
  exact hF (omega3_le_omega3F ((mem_omega3_iff x₁).mpr h))

theorem subB_aL (hc : c < 2) : subB (aL c) (elemsOf (aL c)) = true := by
  rcases cenB_spec hc _ (xsB_spec hc).1 with h | ⟨h, -⟩
  · exact absurd h (xsS_not_mem_om3E hc)
  · exact h

theorem mem_cenA_iff (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (a : GL (Fin 8) (ZMod 2)) :
    a ∈ cenA c x₀ ↔ colsOf (a : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf (aL c) := by
  rw [cenA, hx₀]
  exact mem_genSub_iff_of (subB_aL hc) (cenAg_unit hc _) a

theorem card_cenA_x0 (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    Nat.card (cenA c x₀) = 60 :=
  card_cenA hc (x0_mem hc hx₀).1 (x0_not_mem_omega3 hc hx₀)

theorem comm_of_mem_cenA (hc : c < 2) {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀) :
    a * x₀ = x₀ * a :=
  Subgroup.mem_centralizer_singleton_iff.mp (cenA_le hc x₀ ha).2

theorem fix_of_mem_cenA (hc : c < 2) {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀)
    {v : Fin 8 → ZMod 2} (hv : (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      (a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← comm_of_mem_cenA hc ha, Units.val_mul,
    ← Matrix.mulVec_mulVec, hv]

theorem fix_of_fix_mul (hc : c < 2) {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀)
    {v : Fin 8 → ZMod 2}
    (hv : (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
        (a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) :
    (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v := by
  have h := fix_of_mem_cenA hc ((cenA c x₀).inv_mem ha) hv
  have e1 : ((a⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rwa [e1] at h

theorem betaB_spec (hc : c < 2) :
    (∀ v < 256, (mv8 (betaC c) v = 0 ↔ v ∈ spanN (imgBasis (xsS c)))) ∧
      (∀ v < 256, evenB (mv8 (betaC c) v) = true) ∧
      ∀ j < 5, mv8 (betaC c) ((fiveS c).getD j 0) = fL.getD j 0 := by
  have h := q1449Check_parts.2.2.2.2.2.2.1
  simp only [betaB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h c (mem_zero_one hc)
  refine ⟨fun v hv => ?_, h2, h3⟩
  have h4 := Bool.eq_iff_iff.mp (h1 v hv)
  rw [beq_iff_eq, List.contains_iff_mem] at h4
  exact h4

theorem betaL_eq (c : ℕ) (v : Fin 8 → ZMod 2) :
    betaL c v = MatNCert.vecN 5 (mv8 (betaC c) (code8 v)) := by
  rw [← betaL_vec8, vec8_code8]

theorem mv8_beta_lt (hc : c < 2) (v : Fin 8 → ZMod 2) : mv8 (betaC c) (code8 v) < 32 := by
  have h := (betaB_spec hc).2.1 _ (code8_lt v)
  simp only [evenB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.2

theorem betaL_eq_zero_iff (hc : c < 2)
    (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) (v : Fin 8 → ZMod 2) :
    betaL c v = 0 ↔ (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v := by
  rw [← mem_span_iff hc hx₀, ← (betaB_spec hc).1 _ (code8_lt v), betaL_eq]
  constructor
  · intro h
    rw [← MatNCert.vecN_zero (n := 5)] at h
    exact MatNCert.vecN_inj (mv8_beta_lt hc v) (by norm_num) h
  · intro h
    rw [h, MatNCert.vecN_zero]

theorem betaL_even (hc : c < 2) (v : Fin 8 → ZMod 2) : ∑ i, betaL c v i = 0 := by
  have h := (betaB_spec hc).2.1 _ (code8_lt v)
  simp only [evenB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rw [betaL_eq, Fin.sum_univ_five]
  simp only [MatNCert.vecN]
  rw [← b2z_xor, ← b2z_xor, ← b2z_xor, ← b2z_xor]
  erw [h.1]
  rfl

theorem betaL_u (hc : c < 2) (j : Fin 5) : betaL c (vec8 ((fiveS c).getD j 0)) = fV j := by
  rw [betaL_vec8, (betaB_spec hc).2.2 j j.2, vecN_fL]

theorem sigB_spec (hc : c < 2) {a : List ℕ} (ha : a ∈ elemsOf (aL c)) :
    (∀ j < 5, mv8 (betaC c) (mv8 a ((fiveS c).getD j 0)) ∈ fL) ∧
      (sigOf c a = [0, 1, 2, 3, 4] → a = one8) := by
  have h := q1449Check_parts.2.2.2.2.2.2.2.1
  simp only [sigB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne, List.contains_iff_mem, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h c (mem_zero_one hc) a ha
  refine ⟨h1, fun hs => ?_⟩
  rcases h2 with h2 | h2
  · exact absurd hs h2
  · exact h2

theorem exists_img_u (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀) (j : Fin 5) :
    ∃ k : Fin 5, betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (vec8 ((fiveS c).getD j 0))) = fV k := by
  obtain ⟨k, hk⟩ := mem_fL ((sigB_spec hc ((mem_cenA_iff hc hx₀ a).mp ha)).1 j j.2)
  refine ⟨k, ?_⟩
  rw [mulVec_vec8, betaL_vec8, ← hk, vecN_fL]

theorem exists_sigma (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ v, betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      permL σ (betaL c v) := by
  classical
  choose τ hτ using exists_img_u hc hx₀ ha
  set u : Fin 5 → (Fin 8 → ZMod 2) := fun j => vec8 ((fiveS c).getD j 0) with hu
  have hker : ∀ v, betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) = 0 →
      betaL c v = 0 := fun v hv => by
    rw [betaL_eq_zero_iff hc hx₀] at hv ⊢
    exact fix_of_fix_mul hc ha hv
  have hinj : Function.Injective τ := by
    intro j j' hjj'
    have h1 : betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (u j + u j')) = 0 := by
      rw [Matrix.mulVec_add, map_add, hτ, hτ, hjj']
      exact CharTwo.add_self_eq_zero _
    have h2 := hker _ h1
    rw [map_add, betaL_u hc, betaL_u hc] at h2
    exact fV_injective (CharTwo.add_eq_zero.mp h2)
  set σ : Equiv.Perm (Fin 5) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)
    with hσ
  refine ⟨σ, fun v => ?_⟩
  set J := Finset.univ.filter (fun j => betaL c v j = 1) with hJ
  have hv : betaL c v = ∑ j ∈ J, fV j := eq_sum_fV _ (betaL_even hc v)
  set w := ∑ j ∈ J, u j with hw
  have hbw : betaL c w = betaL c v := by
    rw [hw, map_sum, hv]
    exact Finset.sum_congr rfl fun j _ => betaL_u hc j
  have hvw : betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (v + w)) = 0 := by
    have h0 : betaL c (v + w) = 0 := by
      rw [map_add, hbw]
      exact CharTwo.add_self_eq_zero _
    rw [betaL_eq_zero_iff hc hx₀] at h0 ⊢
    exact fix_of_mem_cenA hc ha h0
  rw [Matrix.mulVec_add, map_add] at hvw
  have hav : betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w) :=
    CharTwo.add_eq_zero.mp hvw
  rw [hav, hw, Matrix.mulVec_sum, map_sum, hv, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hτ, permL_fV]
  rfl

theorem sigma_unique (hc : c < 2) {a : GL (Fin 8) (ZMod 2)} {σ σ' : Equiv.Perm (Fin 5)}
    (h : ∀ v, betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) = permL σ (betaL c v))
    (h' : ∀ v, betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) = permL σ' (betaL c v)) :
    σ = σ' := by
  ext j
  have := (h (vec8 ((fiveS c).getD j 0))).symm.trans (h' (vec8 ((fiveS c).getD j 0)))
  rw [betaL_u hc, permL_fV, permL_fV] at this
  exact congrArg Fin.val (fV_injective this)

theorem eq_one_of_beta (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀)
    (h : ∀ v, betaL c ((a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) = betaL c v) : a = 1 := by
  have hmem := (mem_cenA_iff hc hx₀ a).mp ha
  have hj : ∀ j < 5, mv8 (betaC c) (mv8 (colsOf (a : Matrix (Fin 8) (Fin 8) (ZMod 2)))
      ((fiveS c).getD j 0)) = fL.getD j 0 := by
    intro j hj
    have h1 := h (vec8 ((fiveS c).getD j 0))
    rw [betaL_u hc ⟨j, hj⟩, mulVec_vec8, betaL_vec8, ← vecN_fL] at h1
    exact MatNCert.vecN_inj (by
      obtain ⟨k, hk⟩ := mem_fL ((sigB_spec hc hmem).1 j hj)
      rw [← hk]
      fin_cases k <;> decide) (by interval_cases j <;> decide) h1
  have hsig : sigOf c (colsOf (a : Matrix (Fin 8) (Fin 8) (ZMod 2))) = [0, 1, 2, 3, 4] := by
    simp only [sigOf]
    rw [show [0, 1, 2, 3, 4] = (List.range 5).map id by rfl]
    refine List.map_congr_left fun j hjr => ?_
    rw [hj j (List.mem_range.mp hjr), idxOf_fL j (List.mem_range.mp hjr), id]
  apply eq_of_colsOf_eq
  rw [(sigB_spec hc hmem).2 hsig, Units.val_one, colsOf_one]

theorem exists_mem_cenA_of (hc : c < 2)
    (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) {b : List ℕ}
    (hb : b ∈ elemsOf (aL c)) :
    ∃ a ∈ cenA c x₀, colsOf (a : Matrix (Fin 8) (Fin 8) (ZMod 2)) = b := by
  have hval := (subB_spec (subB_aL hc)).1
  obtain ⟨w, rfl⟩ := mem_elemsOf hb
  obtain ⟨u, hu, hu'⟩ := exists_evalW (aL c) (subB_spec (subB_aL hc)).2.2.2.2
    (cenAg_unit hc _) w
  refine ⟨u, ?_, ?_⟩
  · rw [cenA, hx₀]
    exact hu
  · rw [hu', colsOf_dec8 (hval _ hb)]

theorem irrB_spec (hc : c < 2) : ∀ v < 256, v ∈ spanN (imgBasis (xsS c)) ∨
    ∀ n < 256, n ∈ spanN ((elemsOf (aL c)).map (fun a => mv8 a v) ++ imgBasis (xsS c)) := by
  have h := q1449Check_parts.2.2.2.2.2.2.2.2.1
  simp only [irrB, List.all_eq_true, Bool.or_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, List.mem_range] at h
  exact h c (mem_zero_one hc)

theorem eq_top_of_irr (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (S : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hS0 : ∀ v, (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v → v ∈ S)
    (hSA : ∀ a ∈ cenA c x₀, ∀ v ∈ S, (a : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v ∈ S)
    {v : Fin 8 → ZMod 2} (hv : v ∈ S) (hv0 : (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v ≠ v)
    (w : Fin 8 → ZMod 2) : w ∈ S := by
  rcases irrB_spec hc (code8 v) (code8_lt v) with h | h
  · exact absurd ((mem_span_iff hc hx₀ v).mp h) hv0
  · have hW := spanN_mem _ S (fun u hu => ?_) (code8 w) (h _ (code8_lt w))
    · rwa [vec8_code8] at hW
    · rcases List.mem_append.mp hu with hu | hu
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hu
        obtain ⟨a, ha, hab⟩ := exists_mem_cenA_of hc hx₀ hb
        rw [← hab, ← mulVec_vec8, vec8_code8]
        exact hSA a ha v hv
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hu
        apply hS0
        rw [x0_fix_iff hc hx₀]
        exact ⟨vec8 (2 ^ j), by rw [vec8_xor, mulVec_vec8, hx₀]⟩

theorem invRkB_spec (hc : c < 2) : ∀ x ∈ gamE c, x = one8 ∨ mul8 x x ≠ one8 ∨
    small64B x = true ∨ fullAltB x = true ∨ ∀ a ∈ o5L c, mul8 a x ≠ mul8 x a := by
  have h := q1449Check_parts.2.2.2.2.2.2.2.2.2
  simp only [invRkB, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h
  intro x hx
  rcases h c (mem_zero_one hc) x hx with (((h1 | h1) | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

theorem invol_cases (hc : c < 2) {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ gam c) (hy1 : y ≠ 1)
    (hyy : y * y = 1) {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ gam c) (ha5 : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hay : a * y = y * a) :
    64 ≤ (Finset.univ.filter fun v : Fin 8 → ZMod 2 =>
        (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v).card ∨
      (fullImgB (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true ∧
        ∀ v, G5Cert.b5V ((y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) v = 0) := by
  classical
  rcases invRkB_spec hc _ ((mem_gam_iff hc y).mp hy) with h | h | h | h | h
  · exact absurd (eq_one_of_colsOf h) hy1
  · exact absurd (by rw [← colsOf_mul, ← Units.val_mul, hyy, Units.val_one, colsOf_one]) h
  · left
    simp only [small64B, Bool.and_eq_true, decide_eq_true_eq] at h
    have hnd := (List.nodup_range (n := 256)).filter
      (fun u => mv8 (colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2))) u == u)
    refine h.2.trans ?_
    rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_image_of_injOn (f := vec8)]
    · refine Finset.card_le_card fun v hv => ?_
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      rw [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [mulVec_vec8, hu.2]⟩
    · intro u hu u' hu' huu'
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hu hu'
      exact vec8_inj hu.1 hu'.1 huu'
  · simp only [fullAltB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      List.mem_range] at h
    refine Or.inr ⟨h.1, fun v => ?_⟩
    rw [← vec8_code8 v, mulVec_vec8, ← b5N_spec, h.2 _ (code8_lt v)]
    rfl
  · exfalso
    refine h (colsOf (a : Matrix (Fin 8) (Fin 8) (ZMod 2))) ?_ ?_
    · refine List.mem_filter.mpr ⟨(mem_gam_iff hc a).mp ha, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      refine ⟨by rw [← colsOf_pow, ha5, Units.val_one, colsOf_one], fun h1 => ha1 ?_⟩
      exact eq_one_of_colsOf h1
    · rw [← colsOf_mul, ← colsOf_mul, ← Units.val_mul, ← Units.val_mul, hay]

end Cert

end CFSG.Quasithin.H13.Q1449Cert
