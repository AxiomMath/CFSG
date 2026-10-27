module

public import CFSG.Quasithin.H13.U3Lag

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

@[expose] def maskXor (a m : ℕ) : ℕ :=
  (List.range 64).foldr (fun c acc => if m.testBit c then acc ||| 2 ^ (c ^^^ a) else acc) 0

theorem testBit_foldr_xor (a m k : ℕ) (l : List ℕ) :
    (l.foldr (fun c acc => if m.testBit c then acc ||| 2 ^ (c ^^^ a) else acc) 0).testBit k =
        true ↔ ∃ c ∈ l, m.testBit c = true ∧ c ^^^ a = k := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.foldr_cons]
    by_cases h : m.testBit c = true
    · simp only [h, ↓reduceIte]
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨c', hc', hm', hg'⟩ | hk)
        · exact ⟨c', List.mem_cons_of_mem _ hc', hm', hg'⟩
        · exact ⟨c, List.mem_cons_self .., h, hk⟩
      · rintro ⟨c', hc', hm', hg'⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inr hg'
        · exact Or.inl ⟨c', hc', hm', hg'⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      constructor
      · rintro ⟨c', hc', hm', hg'⟩
        exact ⟨c', List.mem_cons_of_mem _ hc', hm', hg'⟩
      · rintro ⟨c', hc', hm', hg'⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact absurd hm' h
        · exact ⟨c', hc', hm', hg'⟩

theorem testBit_maskXor (a m k : ℕ) :
    (maskXor a m).testBit k = true ↔ ∃ c < 64, m.testBit c = true ∧ c ^^^ a = k := by
  rw [maskXor, testBit_foldr_xor]
  simp only [List.mem_range]

@[expose] def spanL (l : List ℕ) : ℕ := l.foldr (fun a m => m ||| maskXor a m) 1

theorem mem_of_spanL {P : Submodule (ZMod 2) W6} :
    ∀ l : List ℕ, (∀ a ∈ l, a < 64 ∧ vecOf a ∈ P) →
      ∀ k < 64, (spanL l).testBit k = true → vecOf k ∈ P := by
  intro l
  induction l with
  | nil =>
    intro _ k _ hk
    have h1 : (1 : ℕ) = 2 ^ 0 := rfl
    rw [spanL, List.foldr_nil, h1, Nat.testBit_two_pow, decide_eq_true_eq] at hk
    rw [← hk, vecOf_zero]
    exact P.zero_mem
  | cons a l ih =>
    intro hl k hk hkb
    have hl' : ∀ b ∈ l, b < 64 ∧ vecOf b ∈ P := fun b hb => hl b (List.mem_cons_of_mem _ hb)
    have ha := hl a List.mem_cons_self
    rw [spanL, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at hkb
    rcases hkb with hkb | hkb
    · exact ih hl' k hk hkb
    · rw [testBit_maskXor] at hkb
      obtain ⟨c, hc, hcb, rfl⟩ := hkb
      rw [vecOf_xor]
      exact P.add_mem (ih hl' c hc hcb) ha.2

@[expose] def v1mask : ℕ := 2 ^ 0 ||| 2 ^ 15

@[expose] def v3mask : ℕ := spanMask3 15 18 39

@[expose] def v5mask : ℕ := 7378753923620182425

noncomputable def V1sub : Submodule (ZMod 2) W6 := Submodule.span (ZMod 2) {vecOf 15}

noncomputable def V5sub : Submodule (ZMod 2) W6 := LinearMap.ker (b0 (vecOf 15))

theorem hasMask_V1sub : HasMask V1sub v1mask := by
  intro c hc
  rw [V1sub, Submodule.mem_span_singleton]
  have h2 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  have hiff : (∃ r : ZMod 2, r • vecOf 15 = vecOf c) ↔ c = 0 ∨ c = 15 := by
    constructor
    · rintro ⟨r, hr⟩
      rcases h2 r with rfl | rfl
      · rw [zero_smul, ← vecOf_zero] at hr
        exact Or.inl (vecOf_injective hc (by norm_num) hr.symm)
      · rw [one_smul] at hr
        exact Or.inr (vecOf_injective hc (by norm_num) hr.symm)
    · rintro (rfl | rfl)
      · exact ⟨0, by rw [zero_smul, vecOf_zero]⟩
      · exact ⟨1, one_smul _ _⟩
  rw [hiff]
  revert c
  decide

theorem hasMask_V3sub' : HasMask V3sub v3mask := by
  have := hasMask_V3sub
  rwa [lag3_length.2] at this

theorem v5mask_spec : ∀ c < 64, v5mask.testBit c = !dotB 15 (vapp b0c c) := by
  decide +kernel

theorem hasMask_V5sub : HasMask V5sub v5mask := by
  intro c hc
  rw [V5sub, LinearMap.mem_ker, b0_vecOf, v5mask_spec c hc]
  cases dotB 15 (vapp b0c c) <;> decide

theorem card_V1sub : Nat.card V1sub = 2 := by
  rw [card_of_hasMask hasMask_V1sub]
  decide

theorem card_V5sub : Nat.card V5sub = 32 := by
  rw [card_of_hasMask hasMask_V5sub]
  decide +kernel

theorem flag_masks : ∀ c < 64, (v1mask.testBit c = true → v2mask.testBit c = true) ∧
    (v2mask.testBit c = true → v3mask.testBit c = true) ∧
    (v3mask.testBit c = true → v5mask.testBit c = true) := by
  decide +kernel

theorem V1sub_le_V2sub : V1sub ≤ V2sub := by
  intro w hw
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [hasMask_V1sub c hc] at hw
  rw [hasMask_V2sub c hc]
  exact (flag_masks c hc).1 hw

theorem V3sub_le_V5sub : V3sub ≤ V5sub := by
  intro w hw
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [hasMask_V3sub' c hc] at hw
  rw [hasMask_V5sub c hc]
  exact (flag_masks c hc).2.2 hw

theorem vecOf_fifteen_mem_V1sub : vecOf 15 ∈ V1sub :=
  Submodule.subset_span (Set.mem_singleton _)

@[expose] def g2c : List ℕ := [10, 46, 47, 4, 9, 22]

@[expose] def g2ic : List ℕ := [6, 23, 8, 22, 63, 11]

noncomputable abbrev xGL : GL (Fin 6) (ZMod 2) := rho6 (wordElem [3])

noncomputable abbrev g2GL : GL (Fin 6) (ZMod 2) := rho6 (wordElem [0, 2])

noncomputable abbrev yGL : GL (Fin 6) (ZMod 2) := rho6 (wordElem [4])

theorem wordMat_codes : wordMat [3] = u6c 3 ∧ wordMat [0, 2] = g2c ∧ wordMat [4] = u6c 4 ∧
    wordMat [3, 3] = u6ci 3 := by
  decide +kernel

theorem coe_xGL : (xGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (u6c 3) := by
  rw [coe_rho6_wordElem, wordMat_codes.1]

theorem coe_xGL_sq : ((xGL * xGL : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    colMat (u6ci 3) := by
  have e : wordElem [3] * wordElem [3] = wordElem [3, 3] := by simp [wordElem]
  rw [← map_mul, e, coe_rho6_wordElem]
  exact congrArg colMat wordMat_codes.2.2.2

theorem coe_g2GL : (g2GL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat g2c := by
  rw [coe_rho6_wordElem, wordMat_codes.2.1]

theorem coe_yGL : (yGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (u6c 4) := by
  rw [coe_rho6_wordElem, wordMat_codes.2.2.1]

theorem coe_inv_of_code {g : GL (Fin 6) (ZMod 2)} {c ci : List ℕ}
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat c) (h : mul6 ci c = id6) :
    ((g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat ci := by
  calc ((g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))
      = (colMat ci * colMat c) * ((g⁻¹ : GL (Fin 6) (ZMod 2)) :
          Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
        rw [← colMat_mul6, h, colMat_id6, Matrix.one_mul]
    _ = colMat ci * ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          ((g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) := by
        rw [Matrix.mul_assoc, hg]
    _ = colMat ci := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem inv_codes : mul6 (u6ci 3) (u6c 3) = id6 ∧ mul6 g2ic g2c = id6 := by
  decide +kernel

theorem coe_xGL_inv : ((xGL⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    colMat (u6ci 3) :=
  coe_inv_of_code coe_xGL inv_codes.1

theorem coe_g2GL_inv : ((g2GL⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    colMat g2ic :=
  coe_inv_of_code coe_g2GL inv_codes.2

theorem xGL_mem : xGL ∈ J6 := ⟨_, rfl⟩

theorem g2GL_mem : g2GL ∈ J6 := ⟨_, rfl⟩

theorem yGL_mem : yGL ∈ J6 := ⟨_, rfl⟩

theorem fix_fifteen_codes : vapp (u6c 3) 15 = 15 ∧ vapp g2c 15 = 15 := by
  decide +kernel

theorem glLin_vecOf {g : GL (Fin 6) (ZMod 2)} {c : List ℕ}
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat c) (v : ℕ) :
    glLin g (vecOf v) = vecOf (vapp c v) := by
  rw [glLin_apply, hg, colMat_mulVec_vecOf]

theorem xGL_fix : glLin xGL (vecOf 15) = vecOf 15 := by
  rw [glLin_vecOf coe_xGL, fix_fifteen_codes.1]

theorem g2GL_fix : glLin g2GL (vecOf 15) = vecOf 15 := by
  rw [glLin_vecOf coe_g2GL, fix_fifteen_codes.2]

theorem W6_sub_eq_add (a b : W6) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (W6_add_self b)]

theorem glLin_vecOf_sub {g : GL (Fin 6) (ZMod 2)} {e : List ℕ}
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e) (c : ℕ) :
    glLin g (vecOf c) - vecOf c = vecOf (vapp e c ^^^ c) := by
  rw [glLin_vecOf hg, W6_sub_eq_add, vecOf_xor]

theorem eq_one_of_fix_codes {g : GL (Fin 6) (ZMod 2)} (h : ∀ c < 64, glLin g (vecOf c) = vecOf c) :
    g = 1 := by
  apply glLin.injective
  ext w : 1
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [h c hc, map_one]
  rfl

@[expose] def s0HullA (e : List ℕ) : Bool :=
  !([15, 18, 39].all (fun d => v1mask.testBit (vapp e d ^^^ d)) &&
      (List.range 64).all (fun c => vapp e (vapp e c) == c) &&
      (List.range 64).all (fun c => vapp e (vapp (u6c 3) (vapp e (vapp (u6ci 3) c))) ==
        vapp (u6c 3) (vapp e (vapp (u6ci 3) (vapp e c)))) &&
      (List.range 64).all (fun c => vapp e (vapp g2c (vapp e (vapp g2ic c))) ==
        vapp g2c (vapp e (vapp g2ic (vapp e c))))) ||
    ((List.range 64).all (fun c => !v3mask.testBit c || vapp e c == c) &&
      (List.range 64).all (fun c => v3mask.testBit (vapp e c ^^^ c)) &&
      (!(List.range 64).any (fun c => vapp e c != c) ||
        (List.range 64).any (fun c => !v1mask.testBit (vapp e c ^^^ c))))

theorem s0HullA_ok : (List.range 64).all (fun i => s0HullA (s0m i)) = true := by
  decide +kernel

theorem s0_hull_codes : ∀ i < 64,
    (∀ d ∈ [15, 18, 39], v1mask.testBit (vapp (s0m i) d ^^^ d) = true) →
    (∀ c < 64, vapp (s0m i) (vapp (s0m i) c) = c) →
    (∀ c < 64, vapp (s0m i) (vapp (u6c 3) (vapp (s0m i) (vapp (u6ci 3) c))) =
      vapp (u6c 3) (vapp (s0m i) (vapp (u6ci 3) (vapp (s0m i) c)))) →
    (∀ c < 64, vapp (s0m i) (vapp g2c (vapp (s0m i) (vapp g2ic c))) =
      vapp g2c (vapp (s0m i) (vapp g2ic (vapp (s0m i) c)))) →
    (∀ c < 64, v3mask.testBit c = true → vapp (s0m i) c = c) ∧
      (∀ c < 64, v3mask.testBit (vapp (s0m i) c ^^^ c) = true) ∧
      ((∃ c < 64, vapp (s0m i) c ≠ c) →
        ∃ c < 64, v1mask.testBit (vapp (s0m i) c ^^^ c) = false) := by
  intro i hi hA hB hC hD
  have h := List.all_eq_true.1 s0HullA_ok i (List.mem_range.2 hi)
  have hA' : [15, 18, 39].all (fun d => v1mask.testBit (vapp (s0m i) d ^^^ d)) = true :=
    List.all_eq_true.2 hA
  have hB' : (List.range 64).all (fun c => vapp (s0m i) (vapp (s0m i) c) == c) = true :=
    List.all_eq_true.2 fun c hc => beq_iff_eq.2 (hB c (List.mem_range.1 hc))
  have hC' : (List.range 64).all (fun c => vapp (s0m i) (vapp (u6c 3) (vapp (s0m i)
      (vapp (u6ci 3) c))) == vapp (u6c 3) (vapp (s0m i) (vapp (u6ci 3) (vapp (s0m i) c)))) =
      true := List.all_eq_true.2 fun c hc => beq_iff_eq.2 (hC c (List.mem_range.1 hc))
  have hD' : (List.range 64).all (fun c => vapp (s0m i) (vapp g2c (vapp (s0m i)
      (vapp g2ic c))) == vapp g2c (vapp (s0m i) (vapp g2ic (vapp (s0m i) c)))) = true :=
    List.all_eq_true.2 fun c hc => beq_iff_eq.2 (hD c (List.mem_range.1 hc))
  rw [s0HullA, hA', hB', hC', hD'] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.all_eq_true, List.any_eq_true, List.any_eq_false,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun c hc hc3 => ?_, fun c hc => h2 c hc, fun ⟨c, hc, hne⟩ => ?_⟩
  · have := h1 c hc
    rw [hc3] at this
    simpa using this
  · rcases h3 with h3 | ⟨c', hc', h3⟩
    · exact absurd (h3 c hc) (by simpa using hne)
    · exact ⟨c', hc', by simpa using h3⟩

theorem s0_hull_codes_b : ∀ i < 64,
    (∀ d ∈ [15, 18, 39], v1mask.testBit (vapp (s0m i) d ^^^ d) = true) →
    (∃ c < 64, v3mask.testBit c = true ∧ vapp (s0m i) c ≠ c) →
    ∃ c < 64, v5mask.testBit c = true ∧ v3mask.testBit (vapp (s0m i) c ^^^ c) = true ∧
      v1mask.testBit (vapp (s0m i) c ^^^ c) = false := by
  decide +kernel

theorem basis_mem_V3sub : ∀ d ∈ [15, 18, 39], vecOf d ∈ V3sub := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> exact (hasMask_V3sub' _ (by norm_num)).2 (by decide)

theorem vapp_xor_lt {e : List ℕ} (he : ∀ c, vapp e c < 64) {c : ℕ} (hc : c < 64) :
    vapp e c ^^^ c < 64 :=
  Nat.xor_lt_two_pow (n := 6) (he c) hc

theorem codes_of_comm_V3 {s : GL (Fin 6) (ZMod 2)} {e : List ℕ}
    (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e) (he : ∀ c, vapp e c < 64)
    (h : ∀ w ∈ V3sub, glLin s w - w ∈ V1sub) :
    ∀ d ∈ [15, 18, 39], v1mask.testBit (vapp e d ^^^ d) = true := by
  intro d hd
  have hd64 : d < 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have := h _ (basis_mem_V3sub d hd)
  rw [glLin_vecOf_sub hs] at this
  exact (hasMask_V1sub _ (vapp_xor_lt he hd64)).1 this

theorem codes_of_mul_eq {s : GL (Fin 6) (ZMod 2)} {e : List ℕ}
    (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e) {g : GL (Fin 6) (ZMod 2)}
    {gc gic : List ℕ} (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat gc)
    (hgi : ((g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat gic)
    (he : ∀ c, vapp e c < 64) (hgc : ∀ c, vapp gc c < 64)
    (h : s * (g * s * g⁻¹) = g * s * g⁻¹ * s) :
    ∀ c < 64, vapp e (vapp gc (vapp e (vapp gic c))) = vapp gc (vapp e (vapp gic (vapp e c))) := by
  intro c hc
  have h1 := congrArg (fun k : GL (Fin 6) (ZMod 2) => glLin k (vecOf c)) h
  simp only [map_mul, LinearEquiv.mul_apply] at h1
  rw [glLin_vecOf hgi, glLin_vecOf hs, glLin_vecOf hg, glLin_vecOf hs, glLin_vecOf hs,
    glLin_vecOf hgi, glLin_vecOf hs, glLin_vecOf hg] at h1
  exact vecOf_injective (he _) (hgc _) h1

theorem s0_hull_a
    {s : GL (Fin 6) (ZMod 2)} (hs : s ∈ S0)
    (h1 : ∀ w ∈ V3sub, glLin s w - w ∈ V1sub) (h2 : s * s = 1)
    (h3 : s * (xGL * s * xGL⁻¹) = xGL * s * xGL⁻¹ * s)
    (h4 : s * (g2GL * s * g2GL⁻¹) = g2GL * s * g2GL⁻¹ * s) :
    (∀ w ∈ V3sub, glLin s w = w) ∧ (∀ w, glLin s w - w ∈ V3sub) ∧
      (s ≠ 1 → ∃ w, glLin s w - w ∉ V1sub) := by
  obtain ⟨i, hi, rfl⟩ := eq_s0GL hs
  have hm := coe_s0GL hi
  have he : ∀ c, vapp (s0m i) c < 64 := vapp_s0m_lt hi
  have hx64 : ∀ c, vapp (u6c 3) c < 64 := vapp_u6c_lt 3
  have hg64 : ∀ c, vapp g2c c < 64 := fun c => by
    rw [← wordMat_codes.2.1]
    exact vapp_lt_of_getD (by decide +kernel) c
  have hsq : ∀ c < 64, vapp (s0m i) (vapp (s0m i) c) = c := by
    intro c hc
    have := congrArg (fun k : GL (Fin 6) (ZMod 2) => glLin k (vecOf c)) h2
    simp only [map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id_eq] at this
    rw [glLin_vecOf hm, glLin_vecOf hm] at this
    exact vecOf_injective (he _) hc this
  obtain ⟨c1, c2, c3⟩ := s0_hull_codes i hi (codes_of_comm_V3 hm he h1) hsq
    (codes_of_mul_eq hm coe_xGL coe_xGL_inv he hx64 h3)
    (codes_of_mul_eq hm coe_g2GL coe_g2GL_inv he hg64 h4)
  refine ⟨fun w hw => ?_, fun w => ?_, fun hne => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := exists_vecOf w
    rw [glLin_vecOf hm, c1 c hc ((hasMask_V3sub' c hc).1 hw)]
  · obtain ⟨c, hc, rfl⟩ := exists_vecOf w
    rw [glLin_vecOf_sub hm]
    exact (hasMask_V3sub' _ (vapp_xor_lt he hc)).2 (c2 c hc)
  · have hex : ∃ c < 64, vapp (s0m i) c ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_one_of_fix_codes fun c hc => by rw [glLin_vecOf hm, hcon c hc])
    obtain ⟨c, hc, hcb⟩ := c3 hex
    refine ⟨vecOf c, ?_⟩
    rw [glLin_vecOf_sub hm]
    intro hmem
    rw [hasMask_V1sub _ (vapp_xor_lt he hc)] at hmem
    rw [hmem] at hcb
    exact absurd hcb (by decide)

theorem s0_hull_b
    {s : GL (Fin 6) (ZMod 2)} (hs : s ∈ S0)
    (h1 : ∀ w ∈ V3sub, glLin s w - w ∈ V1sub) (h2 : ∃ w ∈ V3sub, glLin s w ≠ w) :
    ∃ w ∈ V5sub, glLin s w - w ∈ V3sub ∧ glLin s w - w ∉ V1sub := by
  obtain ⟨i, hi, rfl⟩ := eq_s0GL hs
  have hm := coe_s0GL hi
  have he : ∀ c, vapp (s0m i) c < 64 := vapp_s0m_lt hi
  have hex : ∃ c < 64, v3mask.testBit c = true ∧ vapp (s0m i) c ≠ c := by
    obtain ⟨w, hw, hne⟩ := h2
    obtain ⟨c, hc, rfl⟩ := exists_vecOf w
    refine ⟨c, hc, (hasMask_V3sub' c hc).1 hw, fun h => hne ?_⟩
    rw [glLin_vecOf hm, h]
  obtain ⟨c, hc, h5, h3, h1'⟩ := s0_hull_codes_b i hi (codes_of_comm_V3 hm he h1) hex
  refine ⟨vecOf c, (hasMask_V5sub c hc).2 h5, ?_, ?_⟩
  · rw [glLin_vecOf_sub hm]
    exact (hasMask_V3sub' _ (vapp_xor_lt he hc)).2 h3
  · rw [glLin_vecOf_sub hm]
    intro hmem
    rw [hasMask_V1sub _ (vapp_xor_lt he hc)] at hmem
    rw [hmem] at h1'
    exact absurd h1' (by decide)

theorem V3_perp_codes : ∀ c < 64, (∀ d ∈ [15, 18, 39], dotB d (vapp b0c c) = false) →
    v3mask.testBit c = true := by
  decide +kernel

theorem sub_V3sub_of_fixes
    {k : GL (Fin 6) (ZMod 2)} (hk : k ∈ N6)
    (hfix : ∀ w ∈ V3sub, glLin k w = w) (w : W6) : glLin k w - w ∈ V3sub := by
  have hb := N6_le_b0Stab hk
  obtain ⟨c, hc, hcw⟩ := exists_vecOf (glLin k w - w)
  rw [← hcw]
  refine (hasMask_V3sub' c hc).2 (V3_perp_codes c hc fun d hd => ?_)
  have hdV := basis_mem_V3sub d hd
  have h0 : b0 (vecOf d) (glLin k w - w) = 0 := by
    rw [map_sub]
    have h1 := b0_mulVec_of_mem_b0Stab hb (vecOf d) w
    rw [← glLin_apply, ← glLin_apply, hfix _ hdV] at h1
    rw [h1, sub_self]
  rw [← hcw, b0_vecOf] at h0
  cases hdot : dotB d (vapp b0c c)
  · rfl
  · rw [hdot] at h0
    exact absurd h0 (by decide)

@[expose] def checkV13 : Bool :=
  (List.range 64).all fun c => !(v3mask.testBit c && !v1mask.testBit c) ||
    (List.range 64).all fun k => !v3mask.testBit k || (spanL [15, c, vapp (u6c 3) c]).testBit k

theorem checkV13_ok : checkV13 = true := by
  decide +kernel

theorem eq_of_V1_le_le_V3 {P : Submodule (ZMod 2) W6} (h1 : V1sub ≤ P) (h3 : P ≤ V3sub)
    (hx : ∀ w ∈ P, glLin xGL w ∈ P) : P = V1sub ∨ P = V3sub := by
  by_cases hP : P ≤ V1sub
  · exact Or.inl (le_antisymm hP h1)
  · right
    refine le_antisymm h3 fun w hw => ?_
    obtain ⟨v, hvP, hv1⟩ := Set.not_subset.1 hP
    obtain ⟨c, hc, rfl⟩ := exists_vecOf v
    obtain ⟨k, hk, rfl⟩ := exists_vecOf w
    have hc3 := (hasMask_V3sub' c hc).1 (h3 hvP)
    have hc1 : v1mask.testBit c = false := by
      cases h : v1mask.testBit c
      · rfl
      · exact absurd ((hasMask_V1sub c hc).2 h) hv1
    have hchk := List.all_eq_true.1 checkV13_ok c (List.mem_range.2 hc)
    simp only [hc3, hc1, Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or,
      List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hchk
    have hk3 := (hasMask_V3sub' k hk).1 hw
    have hspan := (hchk k hk).resolve_left (by rw [hk3]; decide)
    refine mem_of_spanL _ (fun a ha => ?_) k hk hspan
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨by norm_num, h1 vecOf_fifteen_mem_V1sub⟩
    · exact ⟨hc, hvP⟩
    · refine ⟨vapp_u6c_lt 3 c, ?_⟩
      rw [← glLin_vecOf coe_xGL]
      exact hx _ hvP

@[expose] def certV3 (c : ℕ) : List ℕ :=
  [15, 18, 39, c, vapp (u6c 3) c, vapp g2c c, vapp (u6c 3) (vapp (u6c 3) c),
    vapp g2c (vapp (u6c 3) c), vapp (u6c 3) (vapp g2c c), vapp g2c (vapp g2c c)]

@[expose] def checkV3 : Bool :=
  ((List.range 64).all fun c => v3mask.testBit c ||
    (List.range 64).all fun k => !v5mask.testBit k || (spanL (certV3 c)).testBit k) &&
  ((List.range 64).all fun c => v5mask.testBit c ||
    (List.range 64).all fun k => (spanL [3, 4, 8, 17, 32, c]).testBit k) &&
  [3, 4, 8, 17, 32].all fun c => v5mask.testBit c

theorem checkV3_ok : checkV3 = true := by
  decide +kernel

theorem vapp_g2c_lt (c : ℕ) : vapp g2c c < 64 :=
  vapp_lt_of_getD (by decide +kernel) c

theorem eq_of_V3_le {P : Submodule (ZMod 2) W6} (h3 : V3sub ≤ P)
    (hx : ∀ w ∈ P, glLin xGL w ∈ P) (hg : ∀ w ∈ P, glLin g2GL w ∈ P) :
    P = V3sub ∨ P = V5sub ∨ P = ⊤ := by
  have hchk := checkV3_ok
  simp only [checkV3, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hchk
  obtain ⟨⟨hA, hB⟩, hC⟩ := hchk
  by_cases hP3 : P ≤ V3sub
  · exact Or.inl (le_antisymm hP3 h3)
  right
  obtain ⟨v, hvP, hv3⟩ := Set.not_subset.1 hP3
  obtain ⟨c, hc, rfl⟩ := exists_vecOf v
  have hc3 : v3mask.testBit c = false := by
    cases h : v3mask.testBit c
    · rfl
    · exact absurd ((hasMask_V3sub' c hc).2 h) hv3
  have hxP : ∀ a < 64, vecOf a ∈ P → vecOf (vapp (u6c 3) a) ∈ P := fun a _ ha => by
    rw [← glLin_vecOf coe_xGL]
    exact hx _ ha
  have hgP : ∀ a < 64, vecOf a ∈ P → vecOf (vapp g2c a) ∈ P := fun a _ ha => by
    rw [← glLin_vecOf coe_g2GL]
    exact hg _ ha
  have hV5 : V5sub ≤ P := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := exists_vecOf w
    have hk5 := (hasMask_V5sub k hk).1 hw
    have hspan := ((hA c hc).resolve_left (by rw [hc3]; decide) k hk).resolve_left
      (by rw [hk5]; decide)
    refine mem_of_spanL _ (fun a ha => ?_) k hk hspan
    have hx1 := hxP c hc hvP
    have hg1 := hgP c hc hvP
    have hxl := vapp_u6c_lt 3 c
    have hgl := vapp_g2c_lt c
    simp only [certV3, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, h3 (basis_mem_V3sub 15 (by simp))⟩
    · exact ⟨by norm_num, h3 (basis_mem_V3sub 18 (by simp))⟩
    · exact ⟨by norm_num, h3 (basis_mem_V3sub 39 (by simp))⟩
    · exact ⟨hc, hvP⟩
    · exact ⟨hxl, hx1⟩
    · exact ⟨hgl, hg1⟩
    · exact ⟨vapp_u6c_lt 3 _, hxP _ hxl hx1⟩
    · exact ⟨vapp_g2c_lt _, hgP _ hxl hx1⟩
    · exact ⟨vapp_u6c_lt 3 _, hxP _ hgl hg1⟩
    · exact ⟨vapp_g2c_lt _, hgP _ hgl hg1⟩
  by_cases hP5 : P ≤ V5sub
  · exact Or.inl (le_antisymm hP5 hV5)
  right
  obtain ⟨v', hvP', hv5⟩ := Set.not_subset.1 hP5
  obtain ⟨c', hc', rfl⟩ := exists_vecOf v'
  have hc5 : v5mask.testBit c' = false := by
    cases h : v5mask.testBit c'
    · rfl
    · exact absurd ((hasMask_V5sub c' hc').2 h) hv5
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨k, hk, rfl⟩ := exists_vecOf w
  have hspan := (hB c' hc').resolve_left (by rw [hc5]; decide) k hk
  refine mem_of_spanL _ (fun a ha => ?_) k hk hspan
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨hc', hvP'⟩
    | exact ⟨by norm_num, hV5 ((hasMask_V5sub _ (by norm_num)).2 (hC _ (by simp)))⟩

theorem fusion_codes : ∀ c < 64, v3mask.testBit c = true → v1mask.testBit c = false →
    v2mask.testBit c = true ∨ v2mask.testBit (vapp (u6c 3) c) = true ∨
      v2mask.testBit (vapp (u6ci 3) c) = true := by
  decide +kernel

theorem exists_fusion {w : W6} (hw : w ∈ V3sub) (hw1 : w ∉ V1sub) :
    w ∈ V2sub ∨ glLin xGL w ∈ V2sub ∨ glLin (xGL * xGL) w ∈ V2sub := by
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  have hc1 : v1mask.testBit c = false := by
    cases h : v1mask.testBit c
    · rfl
    · exact absurd ((hasMask_V1sub c hc).2 h) hw1
  rcases fusion_codes c hc ((hasMask_V3sub' c hc).1 hw) hc1 with h | h | h
  · exact Or.inl ((hasMask_V2sub c hc).2 h)
  · right; left
    rw [glLin_vecOf coe_xGL]
    exact (hasMask_V2sub _ (vapp_u6c_lt 3 c)).2 h
  · right; right
    rw [glLin_vecOf coe_xGL_sq]
    exact (hasMask_V2sub _ (vapp_lt_of_getD (by decide +kernel) c)).2 h

theorem xGL_pow_four : xGL * xGL * (xGL * xGL) = xGL := by
  apply Units.ext
  rw [Units.val_mul, coe_xGL_sq, coe_xGL, ← colMat_mul6]
  exact congrArg colMat (by decide +kernel)

theorem yGL_codes : maskImg (u6c 4) v2mask = v2mask ∧ v5mask.testBit 4 = true ∧
    v5mask.testBit (vapp (u6c 4) 4) = false := by
  decide +kernel

theorem map_V2sub_yGL : V2sub.map (glLin yGL : W6 →ₗ[ZMod 2] W6) = V2sub := by
  have h := hasMask_map hasMask_V2sub coe_yGL (vapp_u6c_lt 4)
  rw [yGL_codes.1] at h
  exact eq_of_hasMask h hasMask_V2sub

theorem yGL_moves_V5sub : vecOf 4 ∈ V5sub ∧ glLin yGL (vecOf 4) ∉ V5sub := by
  refine ⟨(hasMask_V5sub 4 (by norm_num)).2 yGL_codes.2.1, ?_⟩
  rw [glLin_vecOf coe_yGL, hasMask_V5sub _ (vapp_u6c_lt 4 4), yGL_codes.2.2]
  decide

@[expose] def hexL : List ℕ :=
  [105, 1285, 8721, 2359425, 12582915, 16843009, 67371265, 75505665, 142610433, 301989921,
    537165825, 1074274305, 2147631105, 2148534273, 2214592545, 42949672965, 154618822785,
    171798691905, 206158430211, 279172874305, 584115552273, 1649267474433, 10995116277765,
    18141941860353, 35192962027521, 74766790688785, 140746078306305, 562967133814785,
    564049498603521, 1196268919455745, 1266637932068865, 3377699720527875, 4503668346912769,
    4538784033013761, 9007267974348801, 9015996421505025, 18014415690399745, 18084767270436865,
    36037593380421633, 36046389339226113, 36310271995674753, 72057869989576705,
    72092778412113921, 74309393851615233, 144396663052567041, 146366987889542145,
    297237575406485505, 306244774661197825, 432345564227567625, 576460756732608513,
    576465150350065665, 577023702256845825, 1152939096792956929, 1153062242095726593,
    2305843014045532161, 2305845208237998081, 2310346608841064961, 4611686293322072065,
    4611687117943209985, 4611967493404114945, 9223374235882225665, 9223376434903384065,
    10376293541461622793]

theorem hexL_closed : ∀ m ∈ hexL, ∀ g ∈ gens7, maskImg g m ∈ hexL := by
  decide +kernel

theorem hexL_fifteen : (∀ m ∈ hexL, m.testBit 15 = true →
    m = spanMask3 15 53 0 ∨ m = spanMask3 15 18 0 ∨ m = spanMask3 15 39 0) ∧
    spanMask3 15 18 0 ∈ hexL ∧ spanMask3 15 39 0 ∈ hexL ∧
    (∀ c < 64, (spanMask3 15 53 0).testBit c = true → v3mask.testBit c = true) ∧
    (∀ c < 64, (spanMask3 15 18 0).testBit c = true → v3mask.testBit c = true) ∧
    (∀ c < 64, (spanMask3 15 39 0).testBit c = true → v3mask.testBit c = true) ∧
    ∀ c < 64, v3mask.testBit c = true → (spanL [15, 18, 39]).testBit c = true := by
  decide +kernel

theorem hasMask_span2 {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    HasMask (Submodule.span (ZMod 2) {vecOf a, vecOf b}) (spanMask3 a b 0) := by
  have h := hasMask_span3 (a := a) (b := b) (c := 0) ha hb (by norm_num)
  have hsp : Submodule.span (ZMod 2) ({vecOf a, vecOf b, vecOf 0} : Set W6) =
      Submodule.span (ZMod 2) {vecOf a, vecOf b} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · rw [vecOf_zero]
        exact zero_mem _
    · exact Submodule.span_mono (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto)
  rw [← hsp]
  exact h

theorem map_V3sub_of_fix
    {k : GL (Fin 6) (ZMod 2)} (hk : k ∈ N6)
    (hfix : glLin k (vecOf 15) = vecOf 15) :
    V3sub.map (glLin k : W6 →ₗ[ZMod 2] W6) = V3sub := by
  obtain ⟨h15, hA, hB, h53, h18, h39, hspan⟩ := hexL_fifteen
  have hline : ∀ {n : GL (Fin 6) (ZMod 2)}, n ∈ N6 → glLin n (vecOf 15) = vecOf 15 →
      ∀ b, b < 64 → spanMask3 15 b 0 ∈ hexL →
        (Submodule.span (ZMod 2) {vecOf 15, vecOf b}).map (glLin n : W6 →ₗ[ZMod 2] W6) ≤
          V3sub := by
    intro n hn hnf b hb hbm
    obtain ⟨m', hm', hP⟩ := exists_hasMask_map_of_closed hexL_closed hn _ _
      (hasMask_span2 (by norm_num) hb) hbm
    have h15m : m'.testBit 15 = true := by
      refine (hP 15 (by norm_num)).1 ⟨vecOf 15, Submodule.subset_span (by simp), ?_⟩
      rw [LinearEquiv.coe_coe, hnf]
    intro w hw
    obtain ⟨c, hc, rfl⟩ := exists_vecOf w
    have hcm := (hP c hc).1 hw
    rw [hasMask_V3sub' c hc]
    rcases h15 m' hm' h15m with rfl | rfl | rfl
    · exact h53 c hc hcm
    · exact h18 c hc hcm
    · exact h39 c hc hcm
  have hV3 : V3sub = Submodule.span (ZMod 2) {vecOf 15, vecOf 18} ⊔
      Submodule.span (ZMod 2) {vecOf 15, vecOf 39} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc, rfl⟩ := exists_vecOf w
      refine mem_of_spanL _ (fun a ha => ?_) c hc (hspan c hc ((hasMask_V3sub' c hc).1 hw))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨by norm_num, Submodule.mem_sup_left (Submodule.subset_span (by simp))⟩
      · exact ⟨by norm_num, Submodule.mem_sup_left (Submodule.subset_span (by simp))⟩
      · exact ⟨by norm_num, Submodule.mem_sup_right (Submodule.subset_span (by simp))⟩
    · refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨c, hc, rfl⟩ := exists_vecOf w
        rw [hasMask_V3sub' c hc]
        exact h18 c hc ((hasMask_span2 (by norm_num) (by norm_num) c hc).1 hw)
      · obtain ⟨c, hc, rfl⟩ := exists_vecOf w
        rw [hasMask_V3sub' c hc]
        exact h39 c hc ((hasMask_span2 (by norm_num) (by norm_num) c hc).1 hw)
  have hle : ∀ {n : GL (Fin 6) (ZMod 2)}, n ∈ N6 → glLin n (vecOf 15) = vecOf 15 →
      V3sub.map (glLin n : W6 →ₗ[ZMod 2] W6) ≤ V3sub := by
    intro n hn hnf
    nth_rewrite 1 [hV3]
    rw [Submodule.map_sup]
    exact sup_le (hline hn hnf 18 (by norm_num) hA) (hline hn hnf 39 (by norm_num) hB)
  refine le_antisymm (hle hk hfix) ?_
  have hki : glLin k⁻¹ (vecOf 15) = vecOf 15 := by
    calc glLin k⁻¹ (vecOf 15) = glLin k⁻¹ (glLin k (vecOf 15)) := by rw [hfix]
      _ = vecOf 15 := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
  have h2 := Submodule.map_mono (f := (glLin k : W6 →ₗ[ZMod 2] W6)) (hle (inv_mem hk) hki)
  rw [← map_glLin_mul, mul_inv_cancel, map_glLin_one] at h2
  exact h2

@[expose] def realTab : List (ℕ × ℕ × List (Fin 5)) :=
  [(18, 39, []), (18, 40, [0]), (18, 53, [0, 3, 2]), (18, 58, [3, 2]), (29, 39, [1]),
    (29, 40, [0, 1]), (29, 53, [1, 3, 2]), (29, 58, [3, 0, 2]), (39, 18, [0, 1, 2]),
    (39, 29, [0, 2]), (39, 53, [0, 3, 3]), (39, 58, [3, 0, 3]), (40, 18, [1, 2]),
    (40, 29, [2]), (40, 53, [1, 3, 3]), (40, 58, [3, 3]), (53, 18, [3, 0]), (53, 29, [3]),
    (53, 39, [2, 3]), (53, 40, [2, 3, 0]), (58, 18, [1, 3]), (58, 29, [0, 3]),
    (58, 39, [1, 2, 3]), (58, 40, [0, 2, 3])]

@[expose] def checkReal : Bool :=
  (List.range 64).all fun a => (List.range 64).all fun b =>
    !(v3mask.testBit a && !v1mask.testBit a && v3mask.testBit b && b != 0 && b != 15 &&
        b != a && b != (a ^^^ 15)) ||
      realTab.any fun t => t.1 == a && t.2.1 == b && vapp (wordMat t.2.2) 15 == 15 &&
        vapp (wordMat t.2.2) 18 == a && vapp (wordMat t.2.2) 39 == b

theorem checkReal_ok : checkReal = true := by
  decide +kernel

theorem exists_real {a b : ℕ} (ha : a < 64) (hb : b < 64) (ha3 : v3mask.testBit a = true)
    (ha1 : v1mask.testBit a = false) (hb3 : v3mask.testBit b = true) (hb0 : b ≠ 0)
    (hb15 : b ≠ 15) (hba : b ≠ a) (hba' : b ≠ a ^^^ 15) :
    ∃ j ∈ J6, glLin j (vecOf 15) = vecOf 15 ∧ glLin j (vecOf 18) = vecOf a ∧
      glLin j (vecOf 39) = vecOf b := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 checkReal_ok a (List.mem_range.2 ha)) b
    (List.mem_range.2 hb)
  have hb0' : (b != 0) = true := bne_iff_ne.2 hb0
  have hb15' : (b != 15) = true := bne_iff_ne.2 hb15
  have hba1 : (b != a) = true := bne_iff_ne.2 hba
  have hba2 : (b != (a ^^^ 15)) = true := bne_iff_ne.2 hba'
  simp only [ha3, ha1, hb3, hb0', hb15', hba1, hba2, Bool.not_false, Bool.and_self,
    Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨t, -, ⟨⟨⟨-, h15⟩, h18⟩, h39⟩⟩ := h
  refine ⟨rho6 (wordElem t.2.2), ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · rw [glLin_vecOf (coe_rho6_wordElem _), h15]
  · rw [glLin_vecOf (coe_rho6_wordElem _), h18]
  · rw [glLin_vecOf (coe_rho6_wordElem _), h39]

end CFSG.Quasithin.H13.U3
