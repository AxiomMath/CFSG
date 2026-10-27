module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModB

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Fischer

@[expose] def Ind3 (x y z : Fin 3 → F4) : Prop :=
  ∀ a b c : F4, a • x + b • y + c • z = 0 → a = 0 ∧ b = 0 ∧ c = 0

@[expose] def indep3 (p q r : ℕ) : Bool :=
  (List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
    (a == 0 && b == 0 && c == 0) || (sV a p ^^^ sV b q ^^^ sV c r) != 0

theorem decF_zero : decF 0 = 0 := by
  have h := congrFun decV_zero 0
  simpa [decV] using h

theorem decF_injective {a b : ℕ} (ha : a < 4) (hb : b < 4) (h : decF a = decF b) : a = b := by
  have := congrArg (fun x : F4 => x.code.val) h
  simpa [code_decF, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem decV_comb {p q r a b c : ℕ} (hp : p < 64) (hq : q < 64) (hr : r < 64) (ha : a < 4)
    (hb : b < 4) (hc : c < 4) :
    decV (sV a p ^^^ sV b q ^^^ sV c r) = decF a • decV p + decF b • decV q + decF c • decV r := by
  rw [decV_xor (xor_lt_64 _ (sV_lt_64 _ ha _ hp) _ (sV_lt_64 _ hb _ hq)) (sV_lt_64 _ hc _ hr),
    decV_xor (sV_lt_64 _ ha _ hp) (sV_lt_64 _ hb _ hq), decV_sV ha hp, decV_sV hb hq,
    decV_sV hc hr]

theorem comb_lt {p q r a b c : ℕ} (hp : p < 64) (hq : q < 64) (hr : r < 64) (ha : a < 4)
    (hb : b < 4) (hc : c < 4) : sV a p ^^^ sV b q ^^^ sV c r < 64 :=
  xor_lt_64 _ (xor_lt_64 _ (sV_lt_64 _ ha _ hp) _ (sV_lt_64 _ hb _ hq)) _ (sV_lt_64 _ hc _ hr)

theorem indep3_iff {p q r : ℕ} (hp : p < 64) (hq : q < 64) (hr : r < 64) :
    indep3 p q r = true ↔ Ind3 (decV p) (decV q) (decV r) := by
  simp only [indep3, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · intro h a b c habc
    have ha := a.code.isLt
    have hb := b.code.isLt
    have hc := c.code.isLt
    have key := h _ ha _ hb _ hc
    rw [eq_decF a, eq_decF b, eq_decF c, ← decV_comb hp hq hr ha hb hc] at habc
    have h0 : sV a.code.val p ^^^ sV b.code.val q ^^^ sV c.code.val r = 0 :=
      decV_injective (comb_lt hp hq hr ha hb hc) (by norm_num) (habc.trans decV_zero.symm)
    rcases key with ⟨⟨h1, h2⟩, h3⟩ | key
    · refine ⟨?_, ?_, ?_⟩
      · rw [eq_decF a, h1, decF_zero]
      · rw [eq_decF b, h2, decF_zero]
      · rw [eq_decF c, h3, decF_zero]
    · exact absurd h0 key
  · intro h a ha b hb c hc
    by_cases h0 : sV a p ^^^ sV b q ^^^ sV c r = 0
    · left
      have e := decV_comb hp hq hr ha hb hc
      rw [h0, decV_zero] at e
      obtain ⟨h1, h2, h3⟩ := h _ _ _ e.symm
      rw [← decF_zero] at h1 h2 h3
      exact ⟨⟨decF_injective ha (by norm_num) h1, decF_injective hb (by norm_num) h2⟩,
        decF_injective hc (by norm_num) h3⟩
    · exact Or.inr h0

theorem Ind3.map {x y z : Fin 3 → F4} (h : Ind3 x y z) (g : Matrix.GeneralLinearGroup (Fin 3) F4) :
    Ind3 ((g : Matrix (Fin 3) (Fin 3) F4).mulVec x) ((g : Matrix (Fin 3) (Fin 3) F4).mulVec y)
      ((g : Matrix (Fin 3) (Fin 3) F4).mulVec z) := by
  intro a b c habc
  apply h a b c
  have e : (g : Matrix (Fin 3) (Fin 3) F4).mulVec (a • x + b • y + c • z) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
    exact habc
  have e2 := congrArg (fun w => ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4).mulVec w) e
  simpa [Matrix.mulVec_mulVec] using e2

theorem Ind3.smul {x y z : Fin 3 → F4} (h : Ind3 x y z) {u v w : F4} (hu : u ≠ 0) (hv : v ≠ 0)
    (hw : w ≠ 0) : Ind3 (u • x) (v • y) (w • z) := by
  intro a b c habc
  rw [smul_smul, smul_smul, smul_smul] at habc
  obtain ⟨h1, h2, h3⟩ := h _ _ _ habc
  exact ⟨(mul_eq_zero.mp h1).resolve_right hu, (mul_eq_zero.mp h2).resolve_right hv,
    (mul_eq_zero.mp h3).resolve_right hw⟩

theorem Ind3.swap12 {x y z : Fin 3 → F4} (h : Ind3 x y z) : Ind3 y x z := by
  intro a b c habc
  obtain ⟨h1, h2, h3⟩ := h b a c (by rw [← habc]; abel)
  exact ⟨h2, h1, h3⟩

theorem Ind3.swap23 {x y z : Fin 3 → F4} (h : Ind3 x y z) : Ind3 x z y := by
  intro a b c habc
  obtain ⟨h1, h2, h3⟩ := h a c b (by rw [← habc]; abel)
  exact ⟨h1, h3, h2⟩

theorem Ind3.exists_comb {x y z : Fin 3 → F4} (h : Ind3 x y z) (w : Fin 3 → F4) :
    ∃ a b c : F4, w = a • x + b • y + c • z := by
  let f : (Fin 3 → F4) → (Fin 3 → F4) := fun t => t 0 • x + t 1 • y + t 2 • z
  have hinj : Function.Injective f := by
    intro s t hst
    have e : (s 0 - t 0) • x + (s 1 - t 1) • y + (s 2 - t 2) • z = 0 := by
      simp only [sub_smul]
      have : f s - f t = 0 := sub_eq_zero.mpr hst
      rw [← this]
      simp only [f]
      abel
    obtain ⟨h0, h1, h2⟩ := h _ _ _ e
    funext i
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj w
  exact ⟨t 0, t 1, t 2, ht.symm⟩

@[expose] def ptc (x : Fin 3 → F4) : ℕ := pn (encV x)

theorem pn_scal_of_ne : ∀ w < 64, w ≠ 0 → ∃ c < 4, c ≠ 0 ∧ pn w = sV c w := by
  decide +kernel

theorem pn_sV : ∀ w < 64, ∀ c < 4, c ≠ 0 → pn (sV c w) = pn w := by decide +kernel

theorem pn_lt : ∀ w < 64, pn w < 64 := by decide +kernel

theorem pn_pn : ∀ w < 64, pn (pn w) = pn w := by decide +kernel

theorem pn_ne_zero : ∀ w < 64, w ≠ 0 → pn w ≠ 0 := by decide +kernel

theorem encV_ne_zero {x : Fin 3 → F4} (hx : x ≠ 0) : encV x ≠ 0 := by
  intro h
  apply hx
  rw [← decV_encV x, h, decV_zero]

theorem ptc_lt (x : Fin 3 → F4) : ptc x < 64 := pn_lt _ (encV_lt x)

theorem decV_ptc {x : Fin 3 → F4} (hx : x ≠ 0) : ∃ c : F4, c ≠ 0 ∧ decV (ptc x) = c • x := by
  obtain ⟨c, hc, hc0, he⟩ := pn_scal_of_ne _ (encV_lt x) (encV_ne_zero hx)
  refine ⟨decF c, decF_ne_zero hc hc0, ?_⟩
  rw [ptc, he, decV_sV hc (encV_lt x), decV_encV]

theorem ptc_smul {c : F4} (hc : c ≠ 0) (x : Fin 3 → F4) : ptc (c • x) = ptc x := by
  have hcl := c.code.isLt
  rw [eq_decF c, ← decV_encV x, ← decV_sV hcl (encV_lt x), ptc, ptc,
    encV_decV (sV_lt_64 _ hcl _ (encV_lt x)), encV_decV (encV_lt x)]
  exact pn_sV _ (encV_lt x) _ hcl (code_ne_zero hc)

theorem eq_smul_of_ptc_eq {x y : Fin 3 → F4} (hx : x ≠ 0) (hy : y ≠ 0) (h : ptc x = ptc y) :
    ∃ c : F4, c ≠ 0 ∧ y = c • x := by
  obtain ⟨c, hc, hc0, he⟩ :=
    pn_eq_imp (encV_lt x) (encV_lt y) (encV_ne_zero hx) (encV_ne_zero hy) h
  refine ⟨decF c, decF_ne_zero hc hc0, ?_⟩
  rw [← decV_encV y, he, decV_sV hc (encV_lt x), decV_encV]

theorem ptc_decV {p : ℕ} (hp : p < 64) (hpn : pn p = p) : ptc (decV p) = p := by
  rw [ptc, encV_decV hp, hpn]

theorem ptc_ptc (x : Fin 3 → F4) : ptc (decV (ptc x)) = ptc x :=
  ptc_decV (ptc_lt x) (pn_pn _ (encV_lt x))

theorem decV_ptc_ne_zero {x : Fin 3 → F4} (hx : x ≠ 0) : decV (ptc x) ≠ 0 :=
  decV_ne_zero (ptc_lt x) (pn_ne_zero _ (encV_lt x) (encV_ne_zero hx))

@[expose] def ptCodes : List ℕ := (List.range 64).filter fun v => v != 0 && pn v == v

@[expose] def arc (l : List ℕ) : Bool :=
  l.all fun p => l.all fun q => l.all fun r => p == q || p == r || q == r || indep3 p q r

@[expose] def onLine (p q : ℕ) : List ℕ :=
  ptCodes.filter fun r => !indep3 p q r

theorem mem_ptCodes_iff : ∀ v < 64, v ∈ ptCodes ↔ v ≠ 0 ∧ pn v = v := by decide +kernel

theorem onLine_length : ∀ p ∈ ptCodes, ∀ q ∈ ptCodes, p ≠ q → (onLine p q).length ≤ 5 := by
  decide +kernel

theorem arc_unique : ∀ q ∈ ptCodes, ∀ r ∈ ptCodes, arc [1, 4, 16, 21, q, r] = true →
    (q = 57 ∧ r = 45) ∨ (q = 45 ∧ r = 57) ∨ q = r ∨ q ∈ [1, 4, 16, 21] ∨
      r ∈ [1, 4, 16, 21] := by
  decide +kernel

theorem decV_std (i : Fin 3) : decV (![1, 4, 16] i) = Pi.single i 1 := by
  fin_cases i <;> funext j <;> fin_cases j <;> apply f4_ext <;> rfl

theorem exists_frame {x₁ x₂ x₃ x₄ : Fin 3 → F4} (h123 : Ind3 x₁ x₂ x₃) (h124 : Ind3 x₁ x₂ x₄)
    (h134 : Ind3 x₁ x₃ x₄) (h234 : Ind3 x₂ x₃ x₄) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) F4,
      (∃ c : F4, c ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) F4).mulVec x₁ = c • decV 1) ∧
      (∃ c : F4, c ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) F4).mulVec x₂ = c • decV 4) ∧
      (∃ c : F4, c ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) F4).mulVec x₃ = c • decV 16) ∧
      (g : Matrix (Fin 3) (Fin 3) F4).mulVec x₄ = decV 21 := by
  obtain ⟨a, b, c, h4⟩ := h123.exists_comb x₄
  have ha : a ≠ 0 := by
    intro ha
    obtain ⟨-, -, h⟩ := h234 b c 1 (by
      rw [h4, ha, zero_smul, zero_add, one_smul]
      rw [← two_smul F4 (b • x₂ + c • x₃), F4.two_eq_zero, zero_smul])
    exact one_ne_zero h
  have hb : b ≠ 0 := by
    intro hb
    obtain ⟨-, -, h⟩ := h134 a c 1 (by
      rw [h4, hb, zero_smul, add_zero, one_smul]
      rw [← two_smul F4 (a • x₁ + c • x₃), F4.two_eq_zero, zero_smul])
    exact one_ne_zero h
  have hc : c ≠ 0 := by
    intro hc
    obtain ⟨-, -, h⟩ := h124 a b 1 (by
      rw [h4, hc, zero_smul, add_zero, one_smul]
      rw [← two_smul F4 (a • x₁ + b • x₂), F4.two_eq_zero, zero_smul])
    exact one_ne_zero h
  let F : Matrix (Fin 3) (Fin 3) F4 := Matrix.of fun i j => (![a • x₁, b • x₂, c • x₃] j) i
  have hF : ∀ t : Fin 3 → F4, F.mulVec t = t 0 • (a • x₁) + t 1 • (b • x₂) + t 2 • (c • x₃) := by
    intro t
    funext i
    simp only [F, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hFinj : Function.Injective F.mulVec := by
    intro s t hst
    rw [hF, hF] at hst
    have e : (s 0 - t 0) • (a • x₁) + (s 1 - t 1) • (b • x₂) + (s 2 - t 2) • (c • x₃) = 0 := by
      simp only [sub_smul]
      rw [← sub_eq_zero] at hst
      rw [← hst]
      abel
    obtain ⟨h0, h1, h2⟩ := (h123.smul ha hb hc) _ _ _ e
    funext i
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2
  obtain ⟨u, hu⟩ := Matrix.mulVec_injective_iff_isUnit.mp hFinj
  have hinv : ∀ t, ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4).mulVec (F.mulVec t) = t := by
    intro t
    rw [Matrix.mulVec_mulVec, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hcol : ∀ (k : Fin 3) (d : F4) (y : Fin 3 → F4), d ≠ 0 →
      F.mulVec (decV (![1, 4, 16] k)) = d • y →
      ∃ c : F4, c ≠ 0 ∧ ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4).mulVec y = c • decV (![1, 4, 16] k) := by
    intro k d y hd e
    refine ⟨d⁻¹, inv_ne_zero hd, ?_⟩
    have e2 := hinv (decV (![1, 4, 16] k))
    rw [e, Matrix.mulVec_smul] at e2
    rw [← e2, smul_smul, inv_mul_cancel₀ hd, one_smul]
  refine ⟨u⁻¹, hcol 0 a x₁ ha ?_, hcol 1 b x₂ hb ?_, hcol 2 c x₃ hc ?_, ?_⟩
  · rw [decV_std, hF]
    simp
  · rw [decV_std, hF]
    simp
  · rw [decV_std, hF]
    simp
  · have h21 : decV 21 = fun _ => 1 := by
      funext j
      fin_cases j <;> apply f4_ext <;> rfl
    have e : F.mulVec (fun _ => 1) = x₄ := by
      rw [hF, h4]
      simp
    rw [← e, hinv, h21]

end CFSG.Quasithin.H13.S127.Mod

end
