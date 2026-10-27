module

public import CFSG.Quasithin.Vol2.Ch9Sec2Hyp

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin.H Matrix

namespace Om4Pt

variable {K : Type} [Field K]

@[expose] def lineM (X₀ : Matrix (Fin 2) (Fin 2) K) : Subgroup (Om4.VM K) where
  carrier := {Y | ∃ c : K, Multiplicative.toAdd Y = c • X₀}
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [toAdd_mul, hc, hd, add_smul]⟩
  one_mem' := ⟨0, by rw [toAdd_one, zero_smul]⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    exact ⟨-c, by rw [toAdd_inv, hc, neg_smul]⟩

@[expose] def perpM (X₀ : Matrix (Fin 2) (Fin 2) K) : Subgroup (Om4.VM K) where
  carrier := {Y | detPolarCh6 X₀ (Multiplicative.toAdd Y) = 0}
  mul_mem' := by
    intro a b ha hb
    show detPolarCh6 X₀ (Multiplicative.toAdd a + Multiplicative.toAdd b) = 0
    rw [detPolarCh6_add_right, ha, hb, add_zero]
  one_mem' := by
    show detPolarCh6 X₀ 0 = 0
    simp [detPolarCh6]
  inv_mem' := by
    intro a ha
    show detPolarCh6 X₀ (-Multiplicative.toAdd a) = 0
    have h := ha
    simp only [Set.mem_ofPred_eq, detPolarCh6] at h ⊢
    simp only [Matrix.neg_apply]
    linear_combination -h

theorem mem_perpM {X₀ : Matrix (Fin 2) (Fin 2) K} {Y : Om4.VM K} :
    Y ∈ perpM X₀ ↔ detPolarCh6 X₀ (Multiplicative.toAdd Y) = 0 := Iff.rfl

@[expose] def dgM (X₀ : Matrix (Fin 2) (Fin 2) K) :
    Subgroup (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) where
  carrier := {γ | (γ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀}
  mul_mem' := by
    intro γ δ hγ hδ
    have hγ' : (γ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀ := hγ
    have hδ' : (δ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (δ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀ := hδ
    show ((γ * δ).1 : Matrix (Fin 2) (Fin 2) K) * X₀ * ((γ * δ).2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    calc (γ.1 : Matrix (Fin 2) (Fin 2) K) * δ.1 * X₀ *
          ((δ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ)
        = γ.1 * ((δ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (δ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) *
            (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = X₀ := by rw [hδ', hγ']
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K).1 :
      Matrix (Fin 2) (Fin 2) K) * X₀ *
      ((1 : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K).2 :
        Matrix (Fin 2) (Fin 2) K)ᵀ = X₀
    simp
  inv_mem' := by
    intro γ hγ
    have hγ' : (γ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀ := hγ
    show ((γ⁻¹).1 : Matrix (Fin 2) (Fin 2) K) * X₀ * ((γ⁻¹).2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀
    simp only [Prod.fst_inv, Prod.snd_inv, Matrix.SpecialLinearGroup.coe_inv]
    have ha : (γ.1 : Matrix (Fin 2) (Fin 2) K).adjugate * (γ.1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [Matrix.adjugate_mul, γ.1.2, one_smul]
    have hb : (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ * ((γ.2 : Matrix (Fin 2) (Fin 2) K).adjugate)ᵀ =
        1 := by
      rw [← Matrix.transpose_mul, Matrix.adjugate_mul, γ.2.2, one_smul, Matrix.transpose_one]
    calc (γ.1 : Matrix (Fin 2) (Fin 2) K).adjugate * X₀ *
          ((γ.2 : Matrix (Fin 2) (Fin 2) K).adjugate)ᵀ
        = (γ.1 : Matrix (Fin 2) (Fin 2) K).adjugate *
            ((γ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) *
            ((γ.2 : Matrix (Fin 2) (Fin 2) K).adjugate)ᵀ := by rw [hγ']
      _ = ((γ.1 : Matrix (Fin 2) (Fin 2) K).adjugate * γ.1) * X₀ *
            ((γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ * ((γ.2 : Matrix (Fin 2) (Fin 2) K).adjugate)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = X₀ := by rw [ha, hb, Matrix.one_mul, Matrix.mul_one]

theorem mem_dgM {X₀ : Matrix (Fin 2) (Fin 2) K}
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K} :
    γ ∈ dgM X₀ ↔
      (γ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X₀ := Iff.rfl

theorem rho_eq_of_mem_lineM {X₀ : Matrix (Fin 2) (Fin 2) K}
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K} (hγ : γ ∈ dgM X₀)
    {Y : Om4.VM K} (hY : Y ∈ lineM X₀) : Om4.rho γ Y = Y := by
  obtain ⟨c, hc⟩ := hY
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho, hc, Matrix.mul_smul, Matrix.smul_mul, mem_dgM.mp hγ]

theorem mem_dgM_of_mem_lineM [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hdet : X₀.det ≠ 0)
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hγ : Om4.rho γ (Multiplicative.ofAdd X₀) ∈ lineM X₀) : γ ∈ dgM X₀ := by
  obtain ⟨c, hc⟩ := hγ
  rw [toAdd_rho, toAdd_ofAdd] at hc
  have hd := congrArg Matrix.det hc
  rw [det_rho γ X₀, Matrix.det_smul, Fintype.card_fin] at hd
  have hc2 : c ^ 2 = 1 := by
    have h1 : (c ^ 2 - 1) * X₀.det = 0 := by rw [sub_mul, ← hd]; ring
    rcases mul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdet
  have hc1 : c = 1 := by
    have h2 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c ^ 2 - 1 - 2 * (c - 1) := by ring
      rw [this, hc2, CharTwo.two_eq_zero]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  rw [hc1, one_smul] at hc
  exact mem_dgM.mpr hc

theorem rho_mem_perpM_iff [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K}
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K} (hγ : γ ∈ dgM X₀)
    (Y : Om4.VM K) : Om4.rho γ Y ∈ perpM X₀ ↔ Y ∈ perpM X₀ := by
  rw [mem_perpM, mem_perpM, toAdd_rho]
  conv_lhs => rw [← mem_dgM.mp hγ]
  rw [detPolar_rho]

@[expose] noncomputable def dgOf (X₀ : Matrix (Fin 2) (Fin 2) K) (hX : X₀.det ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) :
    SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K :=
  (g, ⟨(X₀⁻¹ * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀)ᵀ, by
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      (g⁻¹).2, mul_one, Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.mpr hX)]⟩)

theorem coe_dgOf_snd (X₀ : Matrix (Fin 2) (Fin 2) K) (hX : X₀.det ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) :
    ((dgOf X₀ hX g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ =
      X₀⁻¹ * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀ := by
  show ((X₀⁻¹ * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀)ᵀ)ᵀ = _
  rw [Matrix.transpose_transpose]

theorem dgOf_fst (X₀ : Matrix (Fin 2) (Fin 2) K) (hX : X₀.det ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) : (dgOf X₀ hX g).1 = g := rfl

theorem toAdd_rho_dgOf (X₀ : Matrix (Fin 2) (Fin 2) K) (hX : X₀.det ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) (Y : Om4.VM K) :
    Multiplicative.toAdd (Om4.rho (dgOf X₀ hX g) Y) =
      (g : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd Y * X₀⁻¹ *
        ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀ := by
  rw [toAdd_rho, coe_dgOf_snd, dgOf_fst]
  simp only [Matrix.mul_assoc]

theorem dgOf_mem (X₀ : Matrix (Fin 2) (Fin 2) K) (hX : X₀.det ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) : dgOf X₀ hX g ∈ dgM X₀ := by
  rw [mem_dgM, coe_dgOf_snd, dgOf_fst]
  have h1 : X₀ * X₀⁻¹ = 1 := Matrix.mul_nonsing_inv X₀ (isUnit_iff_ne_zero.mpr hX)
  have h2 : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc (g : Matrix (Fin 2) (Fin 2) K) * X₀ *
        (X₀⁻¹ * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀)
      = (g : Matrix (Fin 2) (Fin 2) K) * (X₀ * X₀⁻¹) *
          ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀ := by
        simp only [Matrix.mul_assoc]
    _ = X₀ := by rw [h1, Matrix.mul_one, h2, Matrix.one_mul]

theorem eq_dgOf_of_mem {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K} (hγ : γ ∈ dgM X₀) :
    γ = dgOf X₀ hX γ.1 := by
  have h := mem_dgM.mp hγ
  have hg : ((γ.1⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (γ.1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h0 : X₀⁻¹ * X₀ = 1 := Matrix.nonsing_inv_mul X₀ (isUnit_iff_ne_zero.mpr hX)
  have hm : (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ =
      ((dgOf X₀ hX γ.1).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    rw [coe_dgOf_snd]
    calc (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ
        = X₀⁻¹ * (((γ.1⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((γ.1 : Matrix (Fin 2) (Fin 2) K) * X₀ * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ)) := by
          rw [Matrix.mul_assoc (γ.1 : Matrix (Fin 2) (Fin 2) K), ← Matrix.mul_assoc _
            (γ.1 : Matrix (Fin 2) (Fin 2) K), hg, Matrix.one_mul, ← Matrix.mul_assoc, h0,
            Matrix.one_mul]
      _ = X₀⁻¹ * ((γ.1⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀ := by
          rw [h, Matrix.mul_assoc]
  have hm' := Matrix.transpose_injective hm
  refine Prod.ext rfl (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  exact congrFun (congrFun hm' i) j

@[expose] noncomputable def dgMEquiv {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0) :
    ↥(dgM X₀) ≃* SpecialLinearGroup (Fin 2) K :=
  MulEquiv.ofBijective ((MonoidHom.fst _ _).comp (dgM X₀).subtype)
    ⟨fun a b hab => Subtype.ext (by
        rw [eq_dgOf_of_mem hX a.2, eq_dgOf_of_mem hX b.2]
        exact congrArg (dgOf X₀ hX) hab),
      fun g => ⟨⟨dgOf X₀ hX g, dgOf_mem X₀ hX g⟩, rfl⟩⟩

theorem eq_smul_one_of_commute {Y : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) * Y =
      Y * (g : Matrix (Fin 2) (Fin 2) K)) : Y = Y 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  let u : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let l : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hu := h u
  have hl := h l
  have hu00 := congrFun (congrFun hu 0) 0
  have hu01 := congrFun (congrFun hu 0) 1
  have hl01 := congrFun (congrFun hl 0) 0
  simp [u, l, Matrix.mul_apply, Fin.sum_univ_two] at hu00 hu01 hl01
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | exact hl01 | exact hu00 | exact hl01.symm | exact hu00.symm |
      linear_combination hu01

theorem trace_eq_zero_of_commute_of_sq [CharP K 2] {g : SpecialLinearGroup (Fin 2) K}
    (hg1 : g ≠ 1) (hg2 : g * g = 1) {Y : Matrix (Fin 2) (Fin 2) K}
    (h : (g : Matrix (Fin 2) (Fin 2) K) * Y = Y * (g : Matrix (Fin 2) (Fin 2) K)) :
    Y 0 0 + Y 1 1 = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (g : Matrix (Fin 2) (Fin 2) K) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg2, Matrix.SpecialLinearGroup.coe_one]
  set a := (g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1
  set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1
  have q00 := congrFun (congrFun hsq 0) 0
  have q01 := congrFun (congrFun hsq 0) 1
  have q10 := congrFun (congrFun hsq 1) 0
  have q11 := congrFun (congrFun hsq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at q00 q01 q10 q11
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have hb : b * (a + d) = 0 := by simp only [a, b, d]; linear_combination q01 - b * h2
  have hc : c * (a + d) = 0 := by simp only [a, c, d]; linear_combination q10 - c * h2
  have ha : a ^ 2 + b * c = 0 := by
    simp only [a, b, c]
    linear_combination q00 + (1 - (g : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
  have hd : d ^ 2 + b * c = 0 := by
    simp only [d, b, c]
    linear_combination q11 + (1 - (g : Matrix (Fin 2) (Fin 2) K) 1 1) * h2
  by_cases hb0 : b = 0
  · by_cases hc0 : c = 0
    · exfalso
      apply hg1
      have ha0 : a = 0 := by
        rw [hb0, zero_mul, add_zero] at ha
        exact pow_eq_zero_iff (by norm_num) |>.mp ha
      have hd0 : d = 0 := by
        rw [hb0, zero_mul, add_zero] at hd
        exact pow_eq_zero_iff (by norm_num) |>.mp hd
      ext i j
      fin_cases i <;> fin_cases j
      · simp only [a] at ha0; simp; linear_combination ha0
      · simp only [b] at hb0; simpa using hb0
      · simp only [c] at hc0; simpa using hc0
      · simp only [d] at hd0; simp; linear_combination hd0
    · have had : a + d = 0 := by
        rcases mul_eq_zero.mp hc with h' | h'
        · exact absurd h' hc0
        · exact h'
      have : c * (Y 0 0 + Y 1 1) = 0 := by
        simp only [a, c, d] at had ⊢
        linear_combination e10 + Y 1 0 * had + ((g : Matrix (Fin 2) (Fin 2) K) 1 0 * Y 1 1 -
          Y 1 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 + Y 1 0) * h2
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hc0
      · exact h'
  · have had : a + d = 0 := by
      rcases mul_eq_zero.mp hb with h' | h'
      · exact absurd h' hb0
      · exact h'
    have : b * (Y 0 0 + Y 1 1) = 0 := by
      simp only [a, b, d] at had ⊢
      linear_combination -e01 + Y 0 1 * had + ((g : Matrix (Fin 2) (Fin 2) K) 0 1 * Y 1 1 -
        Y 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 + Y 0 1) * h2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hb0
    · exact h'

theorem sq_eq_zero_of_trace_det [CharP K 2] {N : Matrix (Fin 2) (Fin 2) K} (htr : N 0 0 + N 1 1 = 0)
    (hdet : N.det = 0) : N * N = 0 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination N 0 0 * htr - hdet
  · linear_combination N 0 1 * htr
  · linear_combination N 1 0 * htr
  · linear_combination N 1 1 * htr - hdet

@[expose] def conjSet (N : Matrix (Fin 2) (Fin 2) K) : Set (Om4.VM K) :=
  {Z | ∃ g : SpecialLinearGroup (Fin 2) K, Multiplicative.toAdd Z =
    (g : Matrix (Fin 2) (Fin 2) K) * N * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)}

theorem conj_mem_conjSet {N : Matrix (Fin 2) (Fin 2) K} {Z : Om4.VM K} (hZ : Z ∈ conjSet N)
    (h : SpecialLinearGroup (Fin 2) K) :
    Multiplicative.ofAdd ((h : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd Z *
      ((h⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ∈ conjSet N := by
  obtain ⟨g, hg⟩ := hZ
  refine ⟨h * g, ?_⟩
  rw [toAdd_ofAdd, hg, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_assoc]

theorem exists_conj_eq_smul_e12 [CharP K 2] {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0)
    (htr : N 0 0 + N 1 1 = 0) (hdet : N.det = 0) :
    ∃ (g : SpecialLinearGroup (Fin 2) K) (q : K), q ≠ 0 ∧
      (g : Matrix (Fin 2) (Fin 2) K) * N * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = q • !![0, 1; 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hdet
  have h11 : N 1 1 = N 0 0 := by linear_combination htr - N 0 0 * h2
  by_cases hq : N 0 1 = 0
  · have hp : N 0 0 = 0 := by
      have : N 0 0 ^ 2 = 0 := by rw [h11, hq] at hdet; linear_combination hdet
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hr : N 1 0 ≠ 0 := by
      intro hr
      apply hN
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
    let w : SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 0], by
      simp [Matrix.det_fin_two_of]; exact CharTwo.neg_eq 1⟩
    refine ⟨w, N 1 0, hr, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hp, hq, h11,
        CharTwo.neg_eq]
  · let t := N 0 0 / N 0 1
    let l : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩
    refine ⟨l, N 0 1, hq, ?_⟩
    have hr : N 1 0 = N 0 0 ^ 2 / N 0 1 := by
      field_simp
      rw [h11] at hdet
      linear_combination -hdet
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [l, t, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h11, hr] <;>
      field_simp <;> simp [one_add_one_eq_two, h2]

theorem smul_e12_mem_conjSet [Fintype K] [CharP K 2] {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0)
    (htr : N 0 0 + N 1 1 = 0) (hdet : N.det = 0) {c : K} (hc : c ≠ 0) :
    Multiplicative.ofAdd (c • !![(0 : K), 1; 0, 0]) ∈ conjSet N := by
  obtain ⟨g₀, q, hq, hg₀⟩ := exists_conj_eq_smul_e12 hN htr hdet
  have hq' : Multiplicative.ofAdd (q • !![(0 : K), 1; 0, 0]) ∈ conjSet N :=
    ⟨g₀, by rw [toAdd_ofAdd, hg₀]⟩
  obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c / q)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at ha
    rcases ha with h | h
    · exact hc h
    · exact hq h
  let d : SpecialLinearGroup (Fin 2) K := ⟨!![a, 0; 0, a⁻¹], by
    simp [Matrix.det_fin_two_of, ha0]⟩
  have h1 := conj_mem_conjSet hq' d
  convert h1 using 2
  rw [toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hc' : c = q * (a * a) := by rw [← ha]; field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d, Matrix.mul_apply, Fin.sum_univ_two, hc']
  ring

theorem mem_closure_conjSet [Fintype K] [CharP K 2] {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0)
    (htr : N 0 0 + N 1 1 = 0) (hdet : N.det = 0) {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : Y 0 0 + Y 1 1 = 0) : Multiplicative.ofAdd Y ∈ Subgroup.closure (conjSet N) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set C := Subgroup.closure (conjSet N) with hC
  have hE12 : ∀ c : K, Multiplicative.ofAdd (c • !![(0 : K), 1; 0, 0]) ∈ C := by
    intro c
    by_cases hc : c = 0
    · rw [hc, zero_smul, ofAdd_zero]
      exact C.one_mem
    · exact Subgroup.subset_closure (smul_e12_mem_conjSet hN htr hdet hc)
  let w : SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 0], by
    simp [Matrix.det_fin_two_of]; exact CharTwo.neg_eq 1⟩
  let l : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hE21 : ∀ c : K, Multiplicative.ofAdd (c • !![(0 : K), 0; 1, 0]) ∈ C := by
    intro c
    by_cases hc : c = 0
    · rw [hc, zero_smul, ofAdd_zero]
      exact C.one_mem
    · apply Subgroup.subset_closure
      have h1 := conj_mem_conjSet (smul_e12_mem_conjSet hN htr hdet hc) w
      convert h1 using 2
      rw [toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [w, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  have hI : ∀ c : K, Multiplicative.ofAdd (c • (1 : Matrix (Fin 2) (Fin 2) K)) ∈ C := by
    intro c
    by_cases hc : c = 0
    · rw [hc, zero_smul, ofAdd_zero]
      exact C.one_mem
    · have h1 : Multiplicative.ofAdd (c • !![(1 : K), 1; 1, 1]) ∈ C := by
        apply Subgroup.subset_closure
        have h1 := conj_mem_conjSet (smul_e12_mem_conjSet hN htr hdet hc) l
        convert h1 using 2
        rw [toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [l, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
      have e : c • (1 : Matrix (Fin 2) (Fin 2) K) = c • !![(1 : K), 1; 1, 1] +
          c • !![(0 : K), 1; 0, 0] + c • !![(0 : K), 0; 1, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> linear_combination -c * h2
      rw [e, ofAdd_add, ofAdd_add]
      exact C.mul_mem (C.mul_mem h1 (hE12 c)) (hE21 c)
  have e : Y = Y 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) + Y 0 1 • !![(0 : K), 1; 0, 0] +
      Y 1 0 • !![(0 : K), 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination hY - Y 0 0 * h2
  rw [e, ofAdd_add, ofAdd_add]
  exact C.mul_mem (C.mul_mem (hI _) (hE12 _)) (hE21 _)

theorem exists_eq_conj_sub [CharP K 2] {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0)
    (htr : N 0 0 + N 1 1 = 0) (hdet : N.det = 0) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ (g : SpecialLinearGroup (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) K), Y 0 0 + Y 1 1 = 0 ∧
      N = (g : Matrix (Fin 2) (Fin 2) K) * Y * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) - Y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨g₀, q, hq, hg₀⟩ := exists_conj_eq_smul_e12 hN htr hdet
  have ha2 : a * a - 1 ≠ 0 := by
    intro h
    apply ha1
    have : (a - 1) * (a - 1) = 0 := by linear_combination h - (a - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  let d : SpecialLinearGroup (Fin 2) K := ⟨!![a, 0; 0, a⁻¹], by
    simp [Matrix.det_fin_two_of, ha0]⟩
  set c := q / (a * a - 1) with hcdef
  set E : Matrix (Fin 2) (Fin 2) K := c • !![(0 : K), 1; 0, 0] with hE
  have hdE : (d : Matrix (Fin 2) (Fin 2) K) * E * ((d⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) - E = q • !![(0 : K), 1; 0, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have hc' : c * (a * a - 1) = q := by rw [hcdef]; exact div_mul_cancel₀ q ha2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d, E]
    linear_combination hc'
  have hg₀i : ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (g₀ : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hg₀i' : (g₀ : Matrix (Fin 2) (Fin 2) K) *
      ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨g₀⁻¹ * d * g₀, ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * E *
    (g₀ : Matrix (Fin 2) (Fin 2) K), ?_, ?_⟩
  · have htrE : Matrix.trace (((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        E * (g₀ : Matrix (Fin 2) (Fin 2) K)) = 0 := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hg₀i', Matrix.one_mul, Matrix.trace_fin_two]
      simp [E]
    rwa [Matrix.trace_fin_two] at htrE
  · have hN' : N = ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (q • !![(0 : K), 1; 0, 0]) * (g₀ : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hg₀]
      simp only [← Matrix.mul_assoc, hg₀i, Matrix.one_mul]
      rw [Matrix.mul_assoc, hg₀i, Matrix.mul_one]
    rw [hN', ← hdE, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_sub,
      Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (g₀ : Matrix (Fin 2) (Fin 2) K) ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), hg₀i', Matrix.one_mul, ← Matrix.mul_assoc
      (g₀ : Matrix (Fin 2) (Fin 2) K), hg₀i', Matrix.one_mul]

theorem detPolar_eq_det_mul_trace [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    (Y : Matrix (Fin 2) (Fin 2) K) :
    detPolarCh6 X₀ Y = X₀.det * ((Y * X₀⁻¹) 0 0 + (Y * X₀⁻¹) 1 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, detPolarCh6]
  field_simp
  linear_combination (Y 0 1 * X₀ 1 0 + Y 1 0 * X₀ 0 1) * h2

theorem mem_perpM_iff_trace [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {Y : Om4.VM K} :
    Y ∈ perpM X₀ ↔
      (Multiplicative.toAdd Y * X₀⁻¹) 0 0 + (Multiplicative.toAdd Y * X₀⁻¹) 1 1 = 0 := by
  rw [mem_perpM, detPolar_eq_det_mul_trace hX]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hX, fun h => by rw [h, mul_zero]⟩

theorem mem_lineM_iff_mul_inv {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0) {Y : Om4.VM K} :
    Y ∈ lineM X₀ ↔ ∃ c : K, Multiplicative.toAdd Y * X₀⁻¹ = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hu : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, Matrix.smul_mul, Matrix.mul_nonsing_inv X₀ hu]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc Multiplicative.toAdd Y = Multiplicative.toAdd Y * X₀⁻¹ * X₀ := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul X₀ hu, Matrix.mul_one]
      _ = c • X₀ := by rw [hc, Matrix.smul_mul, Matrix.one_mul]

theorem toAdd_rho_dgOf_mul_inv {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) (Y : Om4.VM K) :
    Multiplicative.toAdd (Om4.rho (dgOf X₀ hX g) Y) * X₀⁻¹ =
      (g : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y * X₀⁻¹) *
        ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [toAdd_rho_dgOf, Matrix.mul_assoc _ X₀, Matrix.mul_nonsing_inv X₀ (isUnit_iff_ne_zero.mpr hX),
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem dgOf_one {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0) : dgOf X₀ hX 1 = 1 := by
  rw [eq_dgOf_of_mem hX (dgM X₀).one_mem]
  rfl

theorem mem_lineM_of_forall_rho_eq {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {Y : Om4.VM K} (h : ∀ γ ∈ dgM X₀, Om4.rho γ Y = Y) : Y ∈ lineM X₀ := by
  rw [mem_lineM_iff_mul_inv hX]
  refine ⟨_, eq_smul_one_of_commute fun g => ?_⟩
  have h1 := congrArg (fun Z => Multiplicative.toAdd Z * X₀⁻¹) (h _ (dgOf_mem X₀ hX g))
  rw [toAdd_rho_dgOf_mul_inv] at h1
  have hg : ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc (g : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y * X₀⁻¹)
      = (g : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y * X₀⁻¹) *
          (((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * g) := by
        rw [hg, Matrix.mul_one]
    _ = Multiplicative.toAdd Y * X₀⁻¹ * g := by rw [← Matrix.mul_assoc, h1]

theorem mem_perpM_of_rho_eq [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K} (hγ : γ ∈ dgM X₀)
    (hγ1 : γ ≠ 1) (hγ2 : γ * γ = 1) {Y : Om4.VM K} (h : Om4.rho γ Y = Y) : Y ∈ perpM X₀ := by
  rw [mem_perpM_iff_trace hX]
  have hγe := eq_dgOf_of_mem hX hγ
  have hg1 : γ.1 ≠ 1 := by
    intro h1
    apply hγ1
    rw [hγe, h1, dgOf_one]
  have hg2 : γ.1 * γ.1 = 1 := by
    have := congrArg Prod.fst hγ2
    simpa using this
  apply trace_eq_zero_of_commute_of_sq hg1 hg2
  have h1 := congrArg (fun Z => Multiplicative.toAdd Z * X₀⁻¹) h
  rw [hγe, toAdd_rho_dgOf_mul_inv] at h1
  have hg : ((γ.1⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (γ.1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc (γ.1 : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y * X₀⁻¹)
      = (γ.1 : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y * X₀⁻¹) *
          (((γ.1⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * γ.1) := by
        rw [hg, Matrix.mul_one]
    _ = Multiplicative.toAdd Y * X₀⁻¹ * γ.1 := by rw [← Matrix.mul_assoc, h1]

@[expose] def rmul (X₀ : Matrix (Fin 2) (Fin 2) K) : Om4.VM K →* Om4.VM K where
  toFun Z := Multiplicative.ofAdd (Multiplicative.toAdd Z * X₀)
  map_one' := by simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp [Matrix.add_mul]

theorem mem_closure_rho [Fintype K] [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {z : Om4.VM K} (hz : z ∈ perpM X₀) (hzd : (Multiplicative.toAdd z).det = 0) (hz1 : z ≠ 1)
    {Y : Om4.VM K} (hY : Y ∈ perpM X₀) :
    Y ∈ Subgroup.closure {W | ∃ γ ∈ dgM X₀, W = Om4.rho γ z} := by
  have hu : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX
  set N := Multiplicative.toAdd z * X₀⁻¹ with hNdef
  have hN : N ≠ 0 := by
    intro h0
    apply hz1
    apply Multiplicative.toAdd.injective
    have : Multiplicative.toAdd z = N * X₀ := by
      rw [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul X₀ hu, Matrix.mul_one]
    rw [this, h0, Matrix.zero_mul, toAdd_one]
  have htr := (mem_perpM_iff_trace hX).mp hz
  have hdet : N.det = 0 := by rw [hNdef, Matrix.det_mul, hzd, zero_mul]
  have h1 := mem_closure_conjSet hN htr hdet ((mem_perpM_iff_trace hX).mp hY)
  have h2 := Subgroup.mem_map_of_mem (rmul X₀) h1
  rw [MonoidHom.map_closure] at h2
  have hYe : rmul X₀ (Multiplicative.ofAdd (Multiplicative.toAdd Y * X₀⁻¹)) = Y := by
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd Y * X₀⁻¹ * X₀ = _
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul X₀ hu, Matrix.mul_one]
  rw [hYe] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨Z, ⟨g, hg⟩, rfl⟩
  refine ⟨dgOf X₀ hX g, dgOf_mem X₀ hX g, ?_⟩
  apply Multiplicative.toAdd.injective
  show Multiplicative.toAdd Z * X₀ = _
  rw [hg, toAdd_rho_dgOf, hNdef]
  simp only [Matrix.mul_assoc]

theorem exists_eq_rho_mul_inv [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {z : Om4.VM K} (hz : z ∈ perpM X₀) (hzd : (Multiplicative.toAdd z).det = 0) (hz1 : z ≠ 1)
    {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ γ ∈ dgM X₀, ∃ Y ∈ perpM X₀, z = Om4.rho γ Y * Y⁻¹ := by
  have hu : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX
  set N := Multiplicative.toAdd z * X₀⁻¹ with hNdef
  have hzN : Multiplicative.toAdd z = N * X₀ := by
    rw [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul X₀ hu, Matrix.mul_one]
  have hN : N ≠ 0 := by
    intro h0
    apply hz1
    apply Multiplicative.toAdd.injective
    rw [hzN, h0, Matrix.zero_mul, toAdd_one]
  have htr := (mem_perpM_iff_trace hX).mp hz
  have hdet : N.det = 0 := by rw [hNdef, Matrix.det_mul, hzd, zero_mul]
  obtain ⟨g, Y', hY', hNe⟩ := exists_eq_conj_sub hN htr hdet ha0 ha1
  refine ⟨dgOf X₀ hX g, dgOf_mem X₀ hX g, Multiplicative.ofAdd (Y' * X₀), ?_, ?_⟩
  · rw [mem_perpM_iff_trace hX, toAdd_ofAdd, Matrix.mul_assoc, Matrix.mul_nonsing_inv X₀ hu,
      Matrix.mul_one]
    exact hY'
  · apply Multiplicative.toAdd.injective
    have hXX : X₀ * X₀⁻¹ = 1 := Matrix.mul_nonsing_inv X₀ hu
    have e1 : (g : Matrix (Fin 2) (Fin 2) K) * (Y' * X₀) * X₀⁻¹ =
        (g : Matrix (Fin 2) (Fin 2) K) * Y' := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hXX, Matrix.mul_one]
    rw [toAdd_mul, toAdd_inv, toAdd_rho_dgOf, toAdd_ofAdd, hzN, hNe, e1, Matrix.sub_mul,
      sub_eq_add_neg]

theorem exists_sl_mul_eq [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    {z : Matrix (Fin 2) (Fin 2) K} (hz : detPolarCh6 X₀ z = 0) (hzd : z.det = 0) :
    ∃ A : SpecialLinearGroup (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K) * X₀ = X₀ + z ∧
      (A : Matrix (Fin 2) (Fin 2) K) * z = z := by
  have hu : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX
  set N := z * X₀⁻¹ with hNdef
  have htr : N 0 0 + N 1 1 = 0 := by
    rw [detPolar_eq_det_mul_trace hX] at hz
    exact (mul_eq_zero.mp hz).resolve_left hX
  have hdet : N.det = 0 := by rw [hNdef, Matrix.det_mul, hzd, zero_mul]
  have hzN : z = N * X₀ := by
    rw [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul X₀ hu, Matrix.mul_one]
  have hdet1 : (1 + N).det = 1 := by
    rw [Matrix.det_fin_two] at hdet ⊢
    simp only [Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    linear_combination htr + hdet
  refine ⟨⟨1 + N, hdet1⟩, ?_, ?_⟩
  · show (1 + N) * X₀ = X₀ + z
    rw [Matrix.add_mul, Matrix.one_mul, ← hzN]
  · show (1 + N) * z = z
    rw [Matrix.add_mul, Matrix.one_mul, hzN, ← Matrix.mul_assoc, sq_eq_zero_of_trace_det htr hdet,
      Matrix.zero_mul, add_zero]

theorem dgM_sup_dgM_eq_top [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K)
    {X₀ X₁ : Matrix (Fin 2) (Fin 2) K} (hX₀ : X₀.det ≠ 0) (hX₁ : X₁.det ≠ 0)
    (hne : ∀ c : K, X₁ ≠ c • X₀) : dgM X₀ ⊔ dgM X₁ = ⊤ := by
  set H := dgM X₀ ⊔ dgM X₁ with hH
  have hXt : X₀ᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hswap : ∀ k : SpecialLinearGroup (Fin 2) K, ((dgOf X₀ᵀ hXt k).2, k) ∈ dgM X₀ := by
    intro k
    have h := mem_dgM.mp (dgOf_mem X₀ᵀ hXt k)
    rw [mem_dgM]
    have h' := congrArg Matrix.transpose h
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, dgOf_fst] at h'
    simpa only [Matrix.mul_assoc] using h'
  set N₂ := H.comap (MonoidHom.inr (SpecialLinearGroup (Fin 2) K) (SpecialLinearGroup (Fin 2) K))
    with hN₂def
  have hN₂ : N₂.Normal := ⟨fun h hh k => by
    rw [Subgroup.mem_comap] at hh ⊢
    have hγ : (((dgOf X₀ᵀ hXt k).2, k) : SpecialLinearGroup (Fin 2) K ×
        SpecialLinearGroup (Fin 2) K) ∈ H := Subgroup.mem_sup_left (hswap k)
    have h1 := H.mul_mem (H.mul_mem hγ hh) (H.inv_mem hγ)
    convert h1 using 1
    ext <;> simp⟩
  have hN₂1 : N₂ ≠ ⊥ := by
    intro hbot
    apply hne ((X₁ * X₀⁻¹) 0 0)
    have hcomm : ∀ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *
        (X₁ * X₀⁻¹) = X₁ * X₀⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) := by
      intro g
      have hmem : (dgOf X₀ hX₀ g⁻¹)⁻¹ * dgOf X₁ hX₁ g⁻¹ ∈ H :=
        H.mul_mem (H.inv_mem (Subgroup.mem_sup_left (dgOf_mem X₀ hX₀ g⁻¹)))
          (Subgroup.mem_sup_right (dgOf_mem X₁ hX₁ g⁻¹))
      have hfst : ((dgOf X₀ hX₀ g⁻¹)⁻¹ * dgOf X₁ hX₁ g⁻¹).1 = 1 := by simp [dgOf_fst]
      have hsnd : ((dgOf X₀ hX₀ g⁻¹)⁻¹ * dgOf X₁ hX₁ g⁻¹).2 ∈ N₂ := by
        rw [Subgroup.mem_comap]
        convert hmem using 1
        exact Prod.ext hfst.symm rfl
      rw [hbot, Subgroup.mem_bot] at hsnd
      have h2 : (dgOf X₀ hX₀ g⁻¹).2 = (dgOf X₁ hX₁ g⁻¹).2 := by
        have := hsnd
        simp only [Prod.snd_mul, Prod.snd_inv] at this
        exact (inv_mul_eq_one.mp this)
      have h3 := congrArg (fun A : SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K)ᵀ) h2
      simp only [coe_dgOf_snd, inv_inv] at h3
      have hu₀ : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX₀
      have hu₁ : IsUnit X₁.det := isUnit_iff_ne_zero.mpr hX₁
      calc (g : Matrix (Fin 2) (Fin 2) K) * (X₁ * X₀⁻¹)
          = X₁ * (X₁⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) * X₁) * X₀⁻¹ := by
            simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv X₁ hu₁, Matrix.one_mul]
        _ = X₁ * (X₀⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) * X₀) * X₀⁻¹ := by rw [h3]
        _ = X₁ * X₀⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) := by
            simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv X₀ hu₀, Matrix.mul_one]
    have hD := eq_smul_one_of_commute hcomm
    calc X₁ = X₁ * X₀⁻¹ * X₀ := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul X₀ (isUnit_iff_ne_zero.mpr hX₀),
            Matrix.mul_one]
      _ = ((X₁ * X₀⁻¹) 0 0 • (1 : Matrix (Fin 2) (Fin 2) K)) * X₀ := congrArg (· * X₀) hD
      _ = (X₁ * X₀⁻¹) 0 0 • X₀ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have htop : N₂ = ⊤ := (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (Om4.sl2_isSimple h4) N₂
    hN₂).resolve_left hN₂1
  refine eq_top_iff.mpr fun γ _ => ?_
  have h1 : ((1 : SpecialLinearGroup (Fin 2) K), (dgOf X₀ hX₀ γ.1).2⁻¹ * γ.2) ∈ H := by
    have : (dgOf X₀ hX₀ γ.1).2⁻¹ * γ.2 ∈ N₂ := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have h2 := H.mul_mem (Subgroup.mem_sup_left (dgOf_mem X₀ hX₀ γ.1)) h1
  convert h2 using 1
  ext <;> simp [dgOf_fst]

theorem toAdd_lr_frM_smul (A B : GL (Fin 2) K) (τ : K ≃+* K) (d : K)
    (Y : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd (d • Y))) =
      τ d • Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd Y)) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_lr, Om4.toAdd_frM,
    Om4.toAdd_frM, toAdd_ofAdd, toAdd_ofAdd]
  have : (d • Y).map τ = τ d • Y.map τ := by
    ext i j
    simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem toAdd_lr_frM_trM_smul (A B : GL (Fin 2) K) (τ : K ≃+* K) (d : K)
    (Y : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K))
      (Multiplicative.ofAdd (d • Y))) = τ d • Multiplicative.toAdd
        ((Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K)) (Multiplicative.ofAdd Y)) := by
  have e1 : ∀ Z : Matrix (Fin 2) (Fin 2) K, (Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K))
      (Multiplicative.ofAdd Z) = (Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd Zᵀ) := fun _ => rfl
  rw [e1, e1, Matrix.transpose_smul, toAdd_lr_frM_smul]

theorem mem_lineM_of_fix {φ : MulAut (Om4.VM K)} {σ : K ≃+* K}
    (hσ : ∀ (d : K) (Y : Matrix (Fin 2) (Fin 2) K), Multiplicative.toAdd (φ (Multiplicative.ofAdd
      (d • Y))) = σ d • Multiplicative.toAdd (φ (Multiplicative.ofAdd Y)))
    {X₀ : Matrix (Fin 2) (Fin 2) K} {c : K} (hc : c ≠ 0)
    (hfix : φ (Multiplicative.ofAdd (c • X₀)) = Multiplicative.ofAdd (c • X₀))
    {Y : Om4.VM K} (hY : Y ∈ lineM X₀) : φ Y ∈ lineM X₀ := by
  obtain ⟨d, hd⟩ := hY
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have h1 : Multiplicative.toAdd (φ (Multiplicative.ofAdd X₀)) = (c / σ c) • X₀ := by
    have h := hσ c X₀
    rw [hfix, toAdd_ofAdd] at h
    rw [div_eq_mul_inv, mul_comm, mul_smul, h, smul_smul, inv_mul_cancel₀ hσc, one_smul]
  refine ⟨σ d * (c / σ c), ?_⟩
  rw [show Y = Multiplicative.ofAdd (d • X₀) by rw [← hd, ofAdd_toAdd], hσ, h1, smul_smul]

theorem det_lr_frM_ne_zero (A B : GL (Fin 2) K) (τ : K ≃+* K) {X₀ : Matrix (Fin 2) (Fin 2) K}
    (hX : X₀.det ≠ 0) :
    (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd X₀))).det ≠ 0 := by
  have hτ : (X₀.map τ).det = τ X₀.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp [map_sub, map_mul]
  rw [MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_frM, toAdd_ofAdd, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hτ]
  refine mul_ne_zero (mul_ne_zero ?_ ((map_ne_zero τ).mpr hX)) ?_
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A) |>.ne_zero
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit B) |>.ne_zero

theorem det_lr_frM_trM_ne_zero (A B : GL (Fin 2) K) (τ : K ≃+* K) {X₀ : Matrix (Fin 2) (Fin 2) K}
    (hX : X₀.det ≠ 0) :
    (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K))
      (Multiplicative.ofAdd X₀))).det ≠ 0 := by
  have e1 : (Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K)) (Multiplicative.ofAdd X₀) =
      (Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd X₀ᵀ) := rfl
  rw [e1]
  exact det_lr_frM_ne_zero A B τ (by rwa [Matrix.det_transpose])

theorem exists_singular_decomp [CharP K 2] {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀.det ≠ 0)
    (c : K) : ∃ Z₁ Z₂ Z₃ : Matrix (Fin 2) (Fin 2) K,
      c • X₀ = Z₁ + Z₂ + Z₃ ∧ detPolarCh6 X₀ Z₁ = 0 ∧ detPolarCh6 X₀ Z₂ = 0 ∧
      detPolarCh6 X₀ Z₃ = 0 ∧ Z₁.det = 0 ∧ Z₂.det = 0 ∧ Z₃.det = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX
  set N₁ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
  set N₂ : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]
  set N₃ : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, 1]
  have hsum : N₁ + N₂ + N₃ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N₁, N₂, N₃] <;> linear_combination h2
  have hX1 : X₀⁻¹ * X₀ = 1 := Matrix.nonsing_inv_mul X₀ hu
  have hXX : ∀ N : Matrix (Fin 2) (Fin 2) K, (c • N * X₀) * X₀⁻¹ = c • N := fun N => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv X₀ hu, Matrix.mul_one]
  refine ⟨c • N₁ * X₀, c • N₂ * X₀, c • N₃ * X₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.add_mul, ← Matrix.add_mul, ← smul_add, ← smul_add, hsum, Matrix.smul_mul,
      Matrix.one_mul]
  · rw [detPolar_eq_det_mul_trace hX, hXX]; simp [N₁]
  · rw [detPolar_eq_det_mul_trace hX, hXX]; simp [N₂]
  · rw [detPolar_eq_det_mul_trace hX, hXX]
    simp [N₃]
    right
    linear_combination c * h2
  · rw [Matrix.det_mul, Matrix.det_smul]; simp [N₁, Matrix.det_fin_two_of]
  · rw [Matrix.det_mul, Matrix.det_smul]; simp [N₂, Matrix.det_fin_two_of]
  · rw [Matrix.det_mul, Matrix.det_smul]; simp [N₃, Matrix.det_fin_two_of]

end Om4Pt

end CFSG.Quasithin.H13.Ch9
