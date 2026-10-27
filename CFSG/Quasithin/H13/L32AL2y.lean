module

public import CFSG.Quasithin.H13.L32AL2x

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

@[expose] def diagS (α : F) (hα : α ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![α, 0; 0, α⁻¹], by simp [Matrix.det_fin_two, hα]⟩

theorem coe_diagS (α : F) (hα : α ≠ 0) :
    ((diagS α hα : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![α, 0; 0, α⁻¹] :=
  rfl

theorem eq_utS_of_pow [Finite F] (h4 : Nat.card F = 4) {g : SpecialLinearGroup (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {k : ℕ} (hk : g ^ (2 ^ k) = 1) :
    g = utS ((g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hgU : IsUT (Matrix.SpecialLinearGroup.toGL g) := hg
  have h1 := hgU.pow_apply_zero_zero (2 ^ k)
  rw [← map_pow, hk, map_one, Units.val_one, Matrix.one_apply_eq] at h1
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := eq_one_of_pow_two_pow h4 h1.symm
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := sl_ut_det hg
    rwa [h00, one_mul] at this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_utS, h00, h11, hg]

theorem mem_sZero_of_borel_pow [Finite F] [CharP F 2] (h4 : Nat.card F = 4)
    {g h : SpecialLinearGroup (Fin 2) F} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {k : ℕ} (hk : rho (g, h) ^ (2 ^ k) = 1) :
    rho (g, h) ∈ sZero := by
  rw [← map_pow, ← map_one rho] at hk
  have hk' := rho_injective hk
  rw [Prod.pow_mk, Prod.one_eq_mk, Prod.mk.injEq] at hk'
  rw [eq_utS_of_pow h4 hg hk'.1, eq_utS_of_pow h4 hh hk'.2]
  exact ⟨_, _, rfl⟩

namespace L2Cfg

variable {Hs Ts Ls Rs O : Subgroup (MulAut (VM F))} {Vs : Subgroup (VM F)} {t : MulAut (VM F)}
  {a : VM F} [Finite F] [CharP F 2]

theorem ls_borel (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {y : MulAut (VM F)} (hy : y ∈ Ls) :
    ∃ g h : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ y = rho (g, h) := by
  obtain ⟨⟨g, h⟩, rfl⟩ := C.hLK hy
  obtain ⟨μ, hμ⟩ := (C.vs_iff _).mp (C.hLV _ hy _ (C.e11_mem 1))
  have e := congrArg Multiplicative.toAdd hμ
  rw [rho_apply, toAdd_lr, toAdd_ofAdd, toAdd_ofAdd, one_smul] at e
  obtain ⟨hg, hh⟩ := isUT_of_mul_e11 (A := Matrix.SpecialLinearGroup.toGL g)
    (B := Matrix.SpecialLinearGroup.toGL h) e
  exact ⟨g, h, hg, hh, rfl⟩

theorem mem_sZero_of_mem_ls (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {y : MulAut (VM F)} (hy : y ∈ Ls)
    {k : ℕ} (hk : y ^ (2 ^ k) = 1) : y ∈ sZero := by
  obtain ⟨g, h, hg, hh, rfl⟩ := C.ls_borel hy
  exact mem_sZero_of_borel_pow C.card hg hh hk

theorem exists_y (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    ∃ g h : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ rho (g, h) ∈ Ls ∧
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 1 := by
  obtain ⟨A, hA, htA, -⟩ := C.exists_A
  obtain ⟨y, hy, v, hv, hyv⟩ := C.hL3
  obtain ⟨g, h, hg, hh, rfl⟩ := C.ls_borel hy
  have hcomm : rho (g, h) * t * (rho (g, h))⁻¹ * t⁻¹ ∈ sZero := by
    obtain ⟨k, hk⟩ := C.hO2 _ (C.hLR _ hy _ C.ht)
    exact C.mem_sZero_of_mem_ls (C.hOL (C.hLR _ hy _ C.ht)) hk
  rw [htA] at hcomm
  have hgh := diag_eq_of_comm hg hh hA hcomm
  obtain ⟨c₀, rfl⟩ := (C.vs_iff v).mp hv
  have hact : rho (g, h) (Multiplicative.ofAdd (c₀ • matE)) =
      Multiplicative.ofAdd (((g : Matrix (Fin 2) (Fin 2) F) 0 0 *
        (h : Matrix (Fin 2) (Fin 2) F) 0 0 * c₀) • matE) := by
    have := apply_smul_e11 (A := Matrix.SpecialLinearGroup.toGL g)
      (B := Matrix.SpecialLinearGroup.toGL h) hg hh 1 c₀
    rw [frM_one, mul_one] at this
    exact this
  refine ⟨g, h, hg, hh, hy, hgh, fun h1 => hyv ?_⟩
  rw [hact, ← hgh, h1, one_mul]

theorem sZero_le (C : L2Cfg F Hs Ts Ls Rs O Vs t a) : sZero ≤ Ls := by
  obtain ⟨g, h, hg, hh, hy, hgh, hαα⟩ := C.exists_y
  set α := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with hα
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hα2 : α ^ 2 + 1 ≠ 0 := by
    intro h0
    apply hαα
    linear_combination h0 - h2
  rintro _ ⟨p, q, rfl⟩
  set p' := p / (α ^ 2 + 1) with hp'
  set q' := q / (α ^ 2 + 1) with hq'
  have hs' : rho (utS p', utS q') ∈ Ts := C.sZero_le_ts ⟨p', q', rfl⟩
  have key : rho (g, h) * rho (utS p', utS q') * (rho (g, h))⁻¹ * (rho (utS p', utS q'))⁻¹ =
      rho (utS p, utS q) := by
    rw [borel_conj_sZero hg hh, ← hgh, ← map_inv, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, utS_inv,
      utS_inv, utS_mul, utS_mul]
    have e1 : α ^ 2 * p' + -p' = p := by
      rw [CharTwo.neg_eq, ← add_one_mul, hp']
      field_simp
    have e2 : α ^ 2 * q' + -q' = q := by
      rw [CharTwo.neg_eq, ← add_one_mul, hq']
      field_simp
    rw [e1, e2]
  rw [← key]
  have h1 : rho (utS p', utS q') * (rho (g, h))⁻¹ * (rho (utS p', utS q'))⁻¹ ∈ Ls :=
    (Subgroup.mem_normalizer_iff.mp (C.hLT hs') _).mp (Ls.inv_mem hy)
  have := Ls.mul_mem hy h1
  simpa only [mul_assoc] using this

theorem exists_diag (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    ∃ (α : F) (hα : α ≠ 0), α * α ≠ 1 ∧ rho (diagS α hα, diagS α hα) ∈ Ls := by
  obtain ⟨g, h, hg, hh, hy, hgh, hαα⟩ := C.exists_y
  have hdet := sl_ut_det hg
  have hdet' := sl_ut_det hh
  obtain ⟨α, hα⟩ : ∃ α : F, α = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := ⟨_, rfl⟩
  rw [← hα] at hdet hαα hgh
  rw [← hgh] at hdet'
  have hα0 : α ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨α, hα0, hαα, ?_⟩
  have hgd : g = diagS α hα0 * utS (α⁻¹ * (g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagS, coe_utS]
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hα]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp
      field_simp
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hg]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp
      exact eq_inv_of_mul_eq_one_right hdet
  have hhd : h = diagS α hα0 * utS (α⁻¹ * (h : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagS, coe_utS]
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hgh]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp
      field_simp
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hh]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp
      exact eq_inv_of_mul_eq_one_right hdet'
  have e : rho (diagS α hα0, diagS α hα0) = rho (g, h) *
      (rho (utS (α⁻¹ * (g : Matrix (Fin 2) (Fin 2) F) 0 1),
        utS (α⁻¹ * (h : Matrix (Fin 2) (Fin 2) F) 0 1)))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, Prod.mk_mul_mk, ← hgd, ← hhd]
  rw [e]
  exact Ls.mul_mem hy (Ls.inv_mem (C.sZero_le ⟨_, _, rfl⟩))

theorem sZero_le_rs (C : L2Cfg F Hs Ts Ls Rs O Vs t a) : sZero ≤ Rs := by
  refine C.hNR _ C.sZero_le (fun y hy => ?_) (fun x hx => ⟨1, by rw [pow_one, pow_two,
    sZero_sq hx]⟩)
  obtain ⟨g, h, hg, hh, rfl⟩ := C.ls_borel hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨p, q, rfl⟩
    rw [borel_conj_sZero hg hh]
    exact ⟨_, _, rfl⟩
  · intro hx
    obtain ⟨p, q, hpq⟩ := hx
    have e : x = (rho (g, h))⁻¹ * rho (utS p, utS q) * rho (g, h) := by
      rw [← hpq]
      group
    rw [e, ← map_inv, Prod.inv_mk]
    have hg' : (((g⁻¹ : SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [hg]
    have hh' : (((h⁻¹ : SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [hh]
    have := borel_conj_sZero hg' hh' p q
    rw [← map_inv, Prod.inv_mk, inv_inv, inv_inv] at this
    rw [this]
    exact ⟨_, _, rfl⟩

theorem exists_three (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    ∃ x ∈ Ls, x ^ 3 = 1 ∧ x ≠ 1 ∧ x a = a := by
  obtain ⟨A, hA, -, c, -, hac⟩ := C.exists_A
  obtain ⟨α, hα0, hαα, hd⟩ := C.exists_diag
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hA11 := hA.apply_ne_zero.2
  set u₀ : F := (A : Matrix (Fin 2) (Fin 2) F) 0 1 / (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hu₀
  set w := rho (utS u₀, (1 : SpecialLinearGroup (Fin 2) F)) with hw
  have hwL : w ∈ Ls := C.sZero_le ⟨u₀, 0, by rw [hw, utS_zero]⟩
  set d := rho (diagS α hα0, diagS α hα0) with hdd
  refine ⟨w⁻¹ * d * w, Ls.mul_mem (Ls.mul_mem (Ls.inv_mem hwL) hd) hwL, ?_, ?_, ?_⟩
  ·
    have hα3 : α ^ 3 = 1 := by
      classical
      have : Fintype F := Fintype.ofFinite F
      have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, C.card]
      have := FiniteField.pow_card_sub_one_eq_one α hα0
      rwa [hcard] at this
    have hd3 : d ^ 3 = 1 := by
      rw [hdd, ← map_pow, Prod.pow_mk]
      have hα3' : α⁻¹ * α⁻¹ * α⁻¹ = 1 := by
        rw [show α⁻¹ * α⁻¹ * α⁻¹ = (α ^ 3)⁻¹ by ring, hα3, inv_one]
      have e : diagS α hα0 ^ 3 = 1 := by
        rw [pow_succ, pow_two]
        ext i j
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagS]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination hα3
        · exact hα3'
      rw [e, ← Prod.one_eq_mk, map_one]
    have e : (w⁻¹ * d * w) ^ 3 = w⁻¹ * d ^ 3 * w := by
      rw [pow_three, pow_three]
      group
    rw [e, hd3, mul_one, inv_mul_cancel]
  · intro h1
    have hd1 : d = 1 := by
      have e : d = w * (w⁻¹ * d * w) * w⁻¹ := by group
      rw [e, h1, mul_one, mul_inv_cancel]
    rw [hdd, ← map_one rho] at hd1
    have := congrArg (fun γ : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F =>
      ((γ.1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) (rho_injective hd1)
    simp [coe_diagS] at this
    exact hαα (by rw [this, one_mul])
  ·
    have hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
    set M' : Matrix (Fin 2) (Fin 2) F := !![0, (A : Matrix (Fin 2) (Fin 2) F) 0 0;
      (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0] with hM'
    have hwa : w a = Multiplicative.ofAdd (c • M') := by
      rw [hac, hw]
      apply Multiplicative.toAdd.injective
      rw [rho_apply, toAdd_lr, toAdd_ofAdd, toAdd_ofAdd]
      change ((utS u₀ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ)) *
          ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ = c • M'
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
        Matrix.mul_smul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp [coe_utS, matJ, hM', hA10, hu₀]
      field_simp
      linear_combination ((A : Matrix (Fin 2) (Fin 2) F) 0 1) * h2
    have hda : d (w a) = w a := by
      rw [hwa, hdd]
      apply Multiplicative.toAdd.injective
      rw [rho_apply, toAdd_lr, toAdd_ofAdd]
      change ((diagS α hα0 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (c • M') * ((diagS α hα0 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ =
          c • M'
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp [coe_diagS, hM'] <;> field_simp
    rw [MulAut.mul_apply, MulAut.mul_apply, hda, ← MulAut.mul_apply, inv_mul_cancel,
      MulAut.one_apply]

theorem vs_le (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    Vs ≤ Subgroup.closure {w | ∃ s ∈ sZero, w = s a} := by
  obtain ⟨A, hA, -, c, hc0, hac⟩ := C.exists_A
  have hA11 := hA.apply_ne_zero.2
  have hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
  intro v hv
  obtain ⟨c', rfl⟩ := (C.vs_iff v).mp hv
  set x : F := c' / (c * (A : Matrix (Fin 2) (Fin 2) F) 1 1) with hx
  set s := rho (utS x, (1 : SpecialLinearGroup (Fin 2) F)) with hs
  have hsZ : s ∈ sZero := ⟨x, 0, by rw [hs, utS_zero]⟩
  have hmem1 : s a ∈ Subgroup.closure {w | ∃ s ∈ sZero, w = s a} :=
    Subgroup.subset_closure ⟨s, hsZ, rfl⟩
  have hmem2 : a ∈ Subgroup.closure {w | ∃ s ∈ sZero, w = s a} :=
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, rfl⟩
  have e : Multiplicative.ofAdd (c' • matE) = s a * a⁻¹ := by
    rw [hac, hs]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, rho_apply, toAdd_lr, toAdd_ofAdd, toAdd_ofAdd]
    change c' • matE = ((utS x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ)) *
        ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ +
          -(c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ))
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] <;>
      simp [coe_utS, matJ, matE, hA10, hx]
    field_simp
  rw [e]
  exact Subgroup.mul_mem _ hmem1 (Subgroup.inv_mem _ hmem2)

end L2Cfg

end CFSG.Quasithin.H13.L32A.L2
