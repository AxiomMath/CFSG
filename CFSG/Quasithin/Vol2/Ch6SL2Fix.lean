module

public import CFSG.Quasithin.Vol2.Ch6Semilinear
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13

variable {F : Type} [Field F]

theorem eq_sl2X_of_mulVec_e1 (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = ![1, 0]) :
    A = sl2X ((A : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h0 := congrFun hA 0
  have h1 := congrFun hA 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hdet := A.2
  rw [Matrix.det_fin_two, h0, h1] at hdet
  simp only [one_mul, mul_zero, sub_zero] at hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2X, h0, h1, hdet]

theorem sl2X_mulVec_e1 (b : F) :
    (sl2X b : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = ![1, 0] := by
  funext i; fin_cases i <;> simp [sl2X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sl2X_mulVec (b : F) (v : Fin 2 → F) :
    (sl2X b : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0 + b * v 1, v 1] := by
  funext i; fin_cases i <;> simp [sl2X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_inv_mulVec (B : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin 2 → F) :
    (B : Matrix (Fin 2) (Fin 2) F).mulVec
      (((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem inv_mulVec_mulVec (B : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin 2 → F) :
    ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      ((B : Matrix (Fin 2) (Fin 2) F).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem exists_sl2_mulVec_single (x : Fin 2 → F) (hx : x ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = x := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i <;> simp_all
    refine ⟨⟨!![0, -(x 1)⁻¹; x 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![x 0, 0; x 1, (x 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq (x y : Fin 2 → F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F).mulVec x = y := by
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_single x hx
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single y hy
  refine ⟨B * A⁻¹, ?_⟩
  have hAinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec x =
      ![1, 0] := by
    rw [← hA, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hAinv, hB]

theorem fixed_eq_line (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hP : P ≠ ⊥)
    {v : Fin 2 → F} (hv : v ≠ 0) (hPv : ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v)
    {w : Fin 2 → F} (hPw : ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w) :
    ∃ c : F, w = c • v := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  set w' := ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w
    with hw'
  have hconj : ∀ A ∈ P, ∃ b : F,
      ((B⁻¹ * A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (sl2X b : Matrix (Fin 2) (Fin 2) F) := by
    intro A hA
    refine ⟨_, congrArg Subtype.val (eq_sl2X_of_mulVec_e1 (B⁻¹ * A * B) ?_)⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB, hPv A hA, ← hB, inv_mulVec_mulVec]
  have hfix' : ∀ A ∈ P, ((B⁻¹ * A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).mulVec w' = w' := by
    intro A hA
    rw [hw', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_inv_mulVec, hPw A hA]
  have hw'1 : w' 1 = 0 := by
    obtain ⟨⟨A, hA⟩, hA1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP
    have hA1 : A ≠ 1 := fun h => hA1' (Subtype.ext h)
    obtain ⟨b, hb⟩ := hconj A hA
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hA1
      have : B⁻¹ * A * B = 1 := by
        apply Subtype.ext
        rw [hb]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2X]
      have := congrArg (fun X => B * X * B⁻¹) this
      simpa [mul_assoc] using this
    have h := hfix' A hA
    rw [hb, sl2X_mulVec] at h
    have := congrFun h 0
    simp at this
    rcases this with h' | h'
    · exact absurd h' hb0
    · exact h'
  refine ⟨w' 0, ?_⟩
  have hw'e : w' = w' 0 • ![1, 0] := by
    funext i; fin_cases i <;> simp [hw'1]
  calc w = (B : Matrix (Fin 2) (Fin 2) F).mulVec w' := by
        rw [hw', mulVec_inv_mulVec]
    _ = w' 0 • v := by
        rw [hw'e, Matrix.mulVec_smul, hB]
        simp

variable [Finite F]

theorem exists_fixed_vector (hF : 2 ∣ Nat.card F)
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hP : IsPGroup 2 P) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥P (Fin 2 → F) :=
    { smul := fun A v => ((A : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec v
      one_smul := fun v => by
        change ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v
        simp
      mul_smul := fun A B v => by
        change ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).mulVec v = _
        rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
        rfl }
  have hcard : 2 ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun, Nat.card_fin]
    exact hF.trans (Dvd.intro _ (by ring))
  have h0 : (0 : Fin 2 → F) ∈ MulAction.fixedPoints ↥P (Fin 2 → F) := fun A =>
    Matrix.mulVec_zero _
  obtain ⟨v, hv, hv0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard h0
  exact ⟨v, fun h => hv0 h.symm, fun A hA => hv ⟨A, hA⟩⟩

@[expose] def det2 (x y : Fin 2 → F) : F := x 0 * y 1 - x 1 * y 0

omit [Finite F] in
theorem eq_add_of_det2_ne_zero {x y : Fin 2 → F} (h : det2 x y ≠ 0) (v : Fin 2 → F) :
    v = ((v 0 * y 1 - v 1 * y 0) / det2 x y) • x + ((x 0 * v 1 - x 1 * v 0) / det2 x y) • y := by
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [det2]; ring
  · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [det2]; ring

omit [Finite F] in
theorem exists_eq_smul_of_det2_eq_zero {w v : Fin 2 → F} (hw : w ≠ 0) (h : det2 w v = 0) :
    ∃ c : F, v = c • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1; apply hw; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨v 1 / w 1, ?_⟩
    simp only [det2, h0, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, h1, false_or] at h
    funext i
    fin_cases i <;> simp [h0, h, h1]
  · refine ⟨v 0 / w 0, ?_⟩
    simp only [det2] at h
    funext i
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem card_fixed_le_semilinear (g : (Fin 2 → F) ≃+ (Fin 2 → F)) (σ : F ≃+* F)
    (hσ : ∀ (a : F) (v : Fin 2 → F), g (a • v) = σ a • g v) (hg : ∃ v, g v ≠ v) :
    Nat.card {v : Fin 2 → F // g v = v} ≤ Nat.card F := by
  classical
  have := Fintype.ofFinite F
  by_cases hind : ∃ x y : Fin 2 → F, g x = x ∧ g y = y ∧ det2 x y ≠ 0
  · obtain ⟨x, y, hx, hy, hxy⟩ := hind
    have hgv : ∀ a b : F, g (a • x + b • y) = σ a • x + σ b • y := by
      intro a b
      rw [map_add, hσ, hσ, hx, hy]
    obtain ⟨θ, hθ⟩ : ∃ θ : F, σ θ ≠ θ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨v, hv⟩ := hg
      apply hv
      rw [eq_add_of_det2_ne_zero hxy v, hgv, hcon, hcon]
    let coord : {v : Fin 2 → F // g v = v} → F := fun v =>
      (v.1 0 * y 1 - v.1 1 * y 0) / det2 x y + (x 0 * v.1 1 - x 1 * v.1 0) / det2 x y * θ
    have hfix : ∀ v : {v : Fin 2 → F // g v = v},
        σ ((v.1 0 * y 1 - v.1 1 * y 0) / det2 x y) = (v.1 0 * y 1 - v.1 1 * y 0) / det2 x y ∧
        σ ((x 0 * v.1 1 - x 1 * v.1 0) / det2 x y) = (x 0 * v.1 1 - x 1 * v.1 0) / det2 x y := by
      intro v
      have h1 := v.2
      rw [eq_add_of_det2_ne_zero hxy v.1, hgv] at h1
      set a := (v.1 0 * y 1 - v.1 1 * y 0) / det2 x y
      set b := (x 0 * v.1 1 - x 1 * v.1 0) / det2 x y
      have hd : ∀ a' b' : F, a' • x + b' • y = 0 → a' = 0 ∧ b' = 0 := by
        intro a' b' h0
        have e0 := congrFun h0 0
        have e1 := congrFun h0 1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
        have hdet : det2 x y ≠ 0 := hxy
        simp only [det2] at hdet
        constructor
        · have : a' * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination y 1 * e0 - y 0 * e1
          exact (mul_eq_zero.mp this).resolve_right hdet
        · have : b' * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination x 0 * e1 - x 1 * e0
          exact (mul_eq_zero.mp this).resolve_right hdet
      have := hd (σ a - a) (σ b - b) (by
        rw [sub_smul, sub_smul]
        have e := h1
        rw [← sub_eq_zero] at e
        rw [← e]
        abel)
      exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩
    have hinj : Function.Injective coord := by
      intro v w hvw
      obtain ⟨hva, hvb⟩ := hfix v
      obtain ⟨hwa, hwb⟩ := hfix w
      set a := (v.1 0 * y 1 - v.1 1 * y 0) / det2 x y
      set b := (x 0 * v.1 1 - x 1 * v.1 0) / det2 x y
      set a' := (w.1 0 * y 1 - w.1 1 * y 0) / det2 x y
      set b' := (x 0 * w.1 1 - x 1 * w.1 0) / det2 x y
      have hc : a + b * θ = a' + b' * θ := hvw
      have hbb : b = b' := by
        by_contra hne
        apply hθ
        have hθe : θ = (a' - a) / (b - b') := by
          have : b - b' ≠ 0 := sub_ne_zero.mpr hne
          field_simp
          linear_combination hc
        rw [hθe, map_div₀, map_sub, map_sub, hva, hwa, hvb, hwb]
      have haa : a = a' := by rw [hbb] at hc; exact add_right_cancel hc
      apply Subtype.ext
      rw [eq_add_of_det2_ne_zero hxy v.1, eq_add_of_det2_ne_zero hxy w.1]
      exact congrArg₂ (· • x + · • y) haa hbb
    exact Nat.card_le_card_of_injective coord hinj
  · push Not at hind
    by_cases h0 : ∃ w : Fin 2 → F, w ≠ 0 ∧ g w = w
    · obtain ⟨w, hw0, hw⟩ := h0
      let c : {v : Fin 2 → F // g v = v} → F := fun v =>
        Classical.choose (exists_eq_smul_of_det2_eq_zero hw0 (hind w v.1 hw v.2))
      have hc : ∀ v, v.1 = c v • w := fun v =>
        Classical.choose_spec (exists_eq_smul_of_det2_eq_zero hw0 (hind w v.1 hw v.2))
      have hinj : Function.Injective c := by
        intro v v' h
        apply Subtype.ext
        rw [hc v, hc v', h]
      exact Nat.card_le_card_of_injective c hinj
    · push Not at h0
      have : ∀ v : {v : Fin 2 → F // g v = v}, v = ⟨0, map_zero g⟩ := by
        intro v
        apply Subtype.ext
        by_contra hv
        exact h0 v.1 hv v.2
      have hsub : Subsingleton {v : Fin 2 → F // g v = v} :=
        ⟨fun a b => (this a).trans (this b).symm⟩
      exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans
        (Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne')

omit [Finite F] in
@[expose] def sl2Stab (v : Fin 2 → F) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v}
  one_mem' := by
    show ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  mul_mem' := by
    intro A B hA hB
    show ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB, hA]
  inv_mem' := by
    intro A hA
    show ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v
    have hA' : (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v := hA
    conv_lhs => rw [← hA']
    exact inv_mulVec_mulVec A v

omit [Finite F] in
theorem mem_sl2Stab {v : Fin 2 → F} {A : Matrix.SpecialLinearGroup (Fin 2) F} :
    A ∈ sl2Stab v ↔ (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v := Iff.rfl

omit [Finite F] in
theorem mem_sl2Stab_iff {v : Fin 2 → F} {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (hB : (B : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    A ∈ sl2Stab v ↔ ∃ b : F, A = B * sl2X b * B⁻¹ := by
  constructor
  · intro hA
    have h1 : B⁻¹ * A * B ∈ sl2Stab ![1, 0] := by
      rw [mem_sl2Stab, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB, hA, ← hB, inv_mulVec_mulVec]
    refine ⟨((B⁻¹ * A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    rw [← eq_sl2X_of_mulVec_e1 _ h1]
    group
  · rintro ⟨b, rfl⟩
    rw [mem_sl2Stab, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hB, inv_mulVec_mulVec, sl2X_mulVec_e1]

omit [Finite F] in
theorem card_sl2Stab {v : Fin 2 → F} (hv : v ≠ 0) : Nat.card (sl2Stab v) = Nat.card F := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  have e : F ≃ ↥(sl2Stab v) :=
    { toFun := fun b => ⟨B * sl2X b * B⁻¹, (mem_sl2Stab_iff hB _).mpr ⟨b, rfl⟩⟩
      invFun := fun A => ((B⁻¹ * (A : Matrix.SpecialLinearGroup (Fin 2) F) * B :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1
      left_inv := fun b => by
        simp only
        rw [show B⁻¹ * (B * sl2X b * B⁻¹) * B = sl2X b by group]
        simp [sl2X]
      right_inv := fun A => by
        apply Subtype.ext
        obtain ⟨b, hb⟩ := (mem_sl2Stab_iff hB A).mp A.2
        simp only
        rw [hb, show B⁻¹ * (B * sl2X b * B⁻¹) * B = sl2X b by group]
        simp [sl2X] }
  exact (Nat.card_congr e).symm

omit [Finite F] in
theorem sub_mem_line_of_mem_sl2Stab {v : Fin 2 → F} (hv : v ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) F} (hA : A ∈ sl2Stab v) (w : Fin 2 → F) :
    ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F).mulVec w - w = c • v := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  obtain ⟨b, rfl⟩ := (mem_sl2Stab_iff hB A).mp hA
  set u := ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w
    with hu
  have hw : w = (B : Matrix (Fin 2) (Fin 2) F).mulVec u := (mulVec_inv_mulVec B w).symm
  refine ⟨b * u 1, ?_⟩
  have hX : (sl2X b : Matrix (Fin 2) (Fin 2) F).mulVec u - u = (b * u 1) • ![1, 0] := by
    rw [sl2X_mulVec]
    funext i; fin_cases i <;> simp
  calc ((B * sl2X b * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec w - w =
      (B : Matrix (Fin 2) (Fin 2) F).mulVec
        ((sl2X b : Matrix (Fin 2) (Fin 2) F).mulVec u - u) := by
        rw [Matrix.mulVec_sub, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← hu, ← hw]
    _ = (b * u 1) • v := by rw [hX, Matrix.mulVec_smul, hB]

theorem det_eq_one_of_pow_eq_one (hF : 2 ∣ Nat.card F) {N : Matrix (Fin 2) (Fin 2) F} {k : ℕ}
    (hN : N ^ 2 ^ k = 1) : N.det = 1 := by
  classical
  have := Fintype.ofFinite F
  have hd : N.det ^ 2 ^ k = 1 := by rw [← Matrix.det_pow, hN, Matrix.det_one]
  have hd0 : N.det ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero k two_ne_zero)] at hd
    exact zero_ne_one hd
  let u : Fˣ := Units.mk0 N.det hd0
  have hu : u ^ 2 ^ k = 1 := Units.ext (by simpa [u] using hd)
  have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Fintype.card Fˣ := orderOf_dvd_card
  rw [Fintype.card_units, ← Nat.card_eq_fintype_card] at h2
  have hodd : Odd (Nat.card F - 1) := by
    have hpos : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
    obtain ⟨m, hm⟩ := hF
    rw [hm]
    have : 1 ≤ 2 * m := hm ▸ hpos
    exact ⟨m - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card F - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hord : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have := congrArg Units.val (orderOf_eq_one_iff.mp hord)
  simpa [u] using this

theorem exists_mem_sl2Stab_of_linear (hF : 2 ∣ Nat.card F) (g : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hlin : ∀ (c : F) (w : Fin 2 → F), g (c • w) = c • g w) {k : ℕ}
    (hpow : ∀ w, g^[2 ^ k] w = w) {v : Fin 2 → F} (hv : g v = v) :
    ∃ A ∈ sl2Stab v, ∀ w, g w = (A : Matrix (Fin 2) (Fin 2) F).mulVec w := by
  classical
  let f : (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := g, map_add' := g.map_add, map_smul' := hlin }
  set N := LinearMap.toMatrix' f with hNdef
  have hNf : ∀ w, N.mulVec w = g w := fun w => LinearMap.toMatrix'_mulVec f w
  have hNpow : ∀ m : ℕ, ∀ w, (N ^ m).mulVec w = g^[m] w := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [pow_succ, ← Matrix.mulVec_mulVec, hNf, ih, Function.iterate_succ_apply]
  have hN1 : N ^ 2 ^ k = 1 := matrix_eq_of_mulVec_eq fun w => by
    rw [hNpow, hpow, Matrix.one_mulVec]
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨N, det_eq_one_of_pow_eq_one hF hN1⟩
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = N := rfl
  refine ⟨A, ?_, fun w => by rw [hA]; exact (hNf w).symm⟩
  show (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v
  rw [hA]
  exact (hNf v).trans hv

end CFSG.Quasithin.H13
