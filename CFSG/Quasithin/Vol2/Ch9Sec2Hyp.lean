module

public import CFSG.Quasithin.Background.HOm4Norm
public import CFSG.Quasithin.Vol2.Ch6OrthHyper

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin.H Matrix

variable {K : Type} [Field K]

@[expose] def uHom (K : Type) [Field K] : Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun c := ⟨!![1, Multiplicative.toAdd c; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    show !![1, Multiplicative.toAdd (1 : Multiplicative K); 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' c d := by
    apply Subtype.ext
    show !![1, Multiplicative.toAdd (c * d); 0, 1] =
      !![1, Multiplicative.toAdd c; 0, 1] * !![1, Multiplicative.toAdd d; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem coe_uHom (c : Multiplicative K) :
    ((uHom K c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, Multiplicative.toAdd c; 0, 1] := rfl

@[expose] def uni (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 2) K) := (uHom K).range

theorem mem_uni_iff {g : SpecialLinearGroup (Fin 2) K} :
    g ∈ uni K ↔ ∃ c : K, (g : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨Multiplicative.ofAdd c, Subtype.ext (by rw [coe_uHom, hc]; rfl)⟩

@[expose] def u1 (K : Type) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem u1_mem : u1 K ∈ uni K := mem_uni_iff.mpr ⟨1, rfl⟩

theorem toAdd_rho (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)
    (X : Om4.VM K) : Multiplicative.toAdd (Om4.rho γ X) =
      (γ.1 : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
        (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

theorem mul_mul_transpose_apply (A M B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (A * M * Bᵀ) i j = A i 0 * (M 0 0 * B j 0 + M 0 1 * B j 1) +
      A i 1 * (M 1 0 * B j 0 + M 1 1 * B j 1) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  ring

theorem det_rho (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    ((γ.1 : Matrix (Fin 2) (Fin 2) K) * X * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ).det = X.det := by
  have h1 : (γ.1 : Matrix (Fin 2) (Fin 2) K).det = 1 := γ.1.2
  have h2 : (γ.2 : Matrix (Fin 2) (Fin 2) K).det = 1 := γ.2.2
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, h2, one_mul, mul_one]

theorem detPolar_rho [CharP K 2] (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)
    (X Y : Matrix (Fin 2) (Fin 2) K) :
    detPolarCh6 ((γ.1 : Matrix (Fin 2) (Fin 2) K) * X * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ)
      ((γ.1 : Matrix (Fin 2) (Fin 2) K) * Y * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) =
      detPolarCh6 X Y := by
  rw [detPolarCh6_eq, detPolarCh6_eq, ← Matrix.add_mul, ← Matrix.mul_add, det_rho, det_rho,
    det_rho]

theorem exists_pairing [Fintype K] [CharP K 2] :
    ∃ τ : K →+ ZMod 2, ∀ X : Matrix (Fin 2) (Fin 2) K, (∀ Y, τ (detPolarCh6 X Y) = 0) → X = 0 := by
  classical
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let τ0 : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  obtain ⟨c, hc⟩ : ∃ c : K, τ0 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Algebra.trace_ne_zero (ZMod 2) K (LinearMap.ext hcon)
  refine ⟨τ0.toAddMonoidHom, fun X hX => ?_⟩
  have hc' : ∀ Y, detPolarCh6 X Y = c → False := fun Y hY => by
    have := hX Y
    rw [hY] at this
    exact hc this
  have h00 : X 0 0 = 0 := by
    by_contra h0
    exact hc' !![0, 0; 0, c * (X 0 0)⁻¹] (by simp [detPolarCh6]; field_simp)
  have h11 : X 1 1 = 0 := by
    by_contra h0
    exact hc' !![c * (X 1 1)⁻¹, 0; 0, 0] (by simp [detPolarCh6]; field_simp)
  have h01 : X 0 1 = 0 := by
    by_contra h0
    exact hc' !![0, 0; c * (X 0 1)⁻¹, 0] (by simp [detPolarCh6]; field_simp)
  have h10 : X 1 0 = 0 := by
    by_contra h0
    exact hc' !![0, c * (X 1 0)⁻¹; 0, 0] (by simp [detPolarCh6]; field_simp)
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem exists_hyperplane [Fintype K] [CharP K 2] {τ : K →+ ZMod 2}
    (hnd : ∀ X : Matrix (Fin 2) (Fin 2) K, (∀ Y, τ (detPolarCh6 X Y) = 0) → X = 0)
    (U : Subgroup (Om4.VM K)) (hU : U.index = 2) :
    ∃ w : Matrix (Fin 2) (Fin 2) K, ∀ Y : Om4.VM K,
      Y ∈ U ↔ τ (detPolarCh6 w (Multiplicative.toAdd Y)) = 0 := by
  let χ : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K →+ ZMod 2 := fun w =>
    { toFun := fun Y => τ (detPolarCh6 w Y)
      map_zero' := by
        have : detPolarCh6 w 0 = 0 := by simp [detPolarCh6]
        simp [this]
      map_add' := fun Y Y' => by simp only [detPolarCh6_add_right, map_add] }
  have hχ : ∀ v w Y, χ (v + w) Y = χ v Y + χ w Y := fun v w Y => by
    simp only [χ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, detPolarCh6_add_left, map_add]
  have h2 : ∀ x : Matrix (Fin 2) (Fin 2) K, x + x = 0 := fun x => by
    ext i j
    exact CharTwo.add_self_eq_zero _
  have hH : ∀ x y, x ∉ U.toAddSubgroup' → y ∉ U.toAddSubgroup' → x + y ∈ U.toAddSubgroup' := by
    intro x y hx hy
    rw [Subgroup.mem_toAddSubgroup'] at hx hy ⊢
    exact (Subgroup.mul_mem_iff_of_index_two hU).mpr (iff_of_false hx hy)
  obtain ⟨w, hw⟩ := exists_ker_eq_of_index_two_ch6 h2 χ hχ hnd U.toAddSubgroup' hH
  refine ⟨w, fun Y => ?_⟩
  have := hw (Multiplicative.toAdd Y)
  rw [Subgroup.mem_toAddSubgroup', _root_.ofAdd_toAdd] at this
  exact this

theorem exists_sl2_mulVec (v : Fin 2 → K) (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![1, 0] := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, (v 1)⁻¹; -v 1, 0], by simp [Matrix.det_fin_two_of, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · refine ⟨⟨!![(v 0)⁻¹, 0; -v 1, v 0], by simp [Matrix.det_fin_two_of, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    ring

theorem exists_rho_eq_single {w : Matrix (Fin 2) (Fin 2) K} (hw : w ≠ 0) (hdet : w.det = 0) :
    ∃ γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K,
      (γ.1 : Matrix (Fin 2) (Fin 2) K) * w * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ =
        !![1, 0; 0, 0] := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  obtain ⟨g, hg1⟩ : ∃ g : SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 = v 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 1 = v 1 := by
    by_cases hb : v 1 = 0
    · have ha : v 0 ≠ 0 := fun ha => hv0 (by ext i; fin_cases i <;> simp [ha, hb])
      exact ⟨⟨!![0, -(v 0)⁻¹; v 0, v 1], by simp [Matrix.det_fin_two_of, hb, ha]⟩, rfl, rfl⟩
    · exact ⟨⟨!![(v 1)⁻¹, 0; v 0, v 1], by simp [Matrix.det_fin_two_of, hb]⟩, rfl, rfl⟩
  set p := (g : Matrix (Fin 2) (Fin 2) K) * w with hp
  have hrow : ∀ j, p 1 j = 0 := by
    intro j
    have h1 := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h1
    simp only [hp, Matrix.mul_apply, Fin.sum_univ_two, hg1.1, hg1.2]
    exact h1
  have hp0 : (fun j => p 0 j) ≠ 0 := by
    intro h0
    apply hw
    have hp' : p = 0 := by
      ext i j
      fin_cases i
      · exact congrFun h0 j
      · exact hrow j
    have := congrArg
      (fun A => ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A)
      hp'
    simp only [hp, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_zero] at this
    exact this
  obtain ⟨h, hh⟩ := exists_sl2_mulVec _ hp0
  refine ⟨(g, h), ?_⟩
  show p * (h : Matrix (Fin 2) (Fin 2) K)ᵀ = _
  have hh0 := congrFun hh 0
  have hh1 := congrFun hh 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh0 hh1
  have e00 : (p * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 = 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply]
    simp only [Matrix.cons_val_zero] at hh0
    linear_combination hh0
  have e01 : (p * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hh1
    linear_combination hh1
  have e10 : (p * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, hrow 0, hrow 1, zero_mul, zero_mul, add_zero]
  have e11 : (p * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 1 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, hrow 0, hrow 1, zero_mul, zero_mul, add_zero]
  ext i j
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

theorem exists_rho_eq_smul_J [Finite K] [CharP K 2] {w : Matrix (Fin 2) (Fin 2) K}
    (hdet : w.det ≠ 0) :
    ∃ (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) (μ : K), μ ≠ 0 ∧
      (γ.1 : Matrix (Fin 2) (Fin 2) K) * w * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ =
        μ • !![0, 1; 1, 0] := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two hK2 w.det
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [hμ, mul_zero])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu : IsUnit w.det := isUnit_iff_ne_zero.mpr hdet
  set g : Matrix (Fin 2) (Fin 2) K := μ • !![0, 1; 1, 0] * w⁻¹ with hg
  have hgdet : g.det = 1 := by
    rw [hg, Matrix.det_mul, Matrix.det_smul, Matrix.det_nonsing_inv, Matrix.det_fin_two_of,
      Fintype.card_fin]
    rw [Ring.inverse_eq_inv']
    have : (0 : K) * 0 - 1 * 1 = 1 := by linear_combination -h2
    rw [this, mul_one, pow_two, ← hμ]
    exact mul_inv_cancel₀ hdet
  refine ⟨(⟨g, hgdet⟩, 1), μ, hμ0, ?_⟩
  show g * w * ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ = _
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one, hg, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem mem_map_rho_iff [CharP K 2] {τ : K →+ ZMod 2} {w : Matrix (Fin 2) (Fin 2) K}
    {U : Subgroup (Om4.VM K)}
    (hU : ∀ Y : Om4.VM K, Y ∈ U ↔ τ (detPolarCh6 w (Multiplicative.toAdd Y)) = 0)
    (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) (Y : Om4.VM K) :
    Y ∈ U.map (Om4.rho γ).toMonoidHom ↔
      τ (detPolarCh6 ((γ.1 : Matrix (Fin 2) (Fin 2) K) * w * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (Multiplicative.toAdd Y)) = 0 := by
  rw [Subgroup.mem_map_equiv, hU]
  have e : Multiplicative.toAdd Y = (γ.1 : Matrix (Fin 2) (Fin 2) K) *
      Multiplicative.toAdd ((Om4.rho γ).symm Y) * (γ.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    rw [← toAdd_rho, MulEquiv.apply_symm_apply]
  rw [e, detPolar_rho]

theorem detPolar_single (Y : Matrix (Fin 2) (Fin 2) K) : detPolarCh6 !![1, 0; 0, 0] Y = Y 1 1 := by
  simp [detPolarCh6]

theorem detPolar_smul_J (μ : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    detPolarCh6 (μ • !![0, 1; 1, 0]) Y = μ * (Y 1 0 + Y 0 1) := by
  simp [detPolarCh6]
  ring

theorem exists_good_conj [Fintype K] [CharP K 2] (U : Subgroup (Om4.VM K)) (hU : U.index = 2) :
    ∃ (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)
      (P : Subgroup (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)),
      P ≤ (uni K).prod (uni K) ∧
      (∀ c : K, Multiplicative.ofAdd !![c, 0; 0, 0] ∈ U.map (Om4.rho γ).toMonoidHom) ∧
      (∀ p ∈ P, ∀ Y ∈ U.map (Om4.rho γ).toMonoidHom,
        Om4.rho p Y ∈ U.map (Om4.rho γ).toMonoidHom) ∧
      (∀ Y : Om4.VM K, (∀ p ∈ P, Om4.rho p Y = Y) → Y ∈ U.map (Om4.rho γ).toMonoidHom) := by
  classical
  obtain ⟨τ, hnd⟩ := exists_pairing (K := K)
  obtain ⟨w, hw⟩ := exists_hyperplane hnd U hU
  have hw0 : w ≠ 0 := by
    rintro rfl
    have htop : U = ⊤ := by
      ext Y
      simp only [hw, Subgroup.mem_top, iff_true]
      simp [detPolarCh6]
    rw [htop, Subgroup.index_top] at hU
    exact absurd hU (by norm_num)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hdet : w.det = 0
  · obtain ⟨γ, hγ⟩ := exists_rho_eq_single hw0 hdet
    have hmem := mem_map_rho_iff hw γ
    simp only [hγ, detPolar_single] at hmem
    refine ⟨γ, (uni K).prod (uni K), le_rfl, fun c => ?_, fun p hp Y hY => ?_, fun Y hY => ?_⟩
    · rw [hmem]
      simp
    · rw [hmem] at hY ⊢
      obtain ⟨c, hc⟩ := mem_uni_iff.mp hp.1
      obtain ⟨c', hc'⟩ := mem_uni_iff.mp hp.2
      rw [toAdd_rho, hc, hc', mul_mul_transpose_apply]
      simpa using hY
    · rw [hmem]
      have h1 : !![(1 : K), 1; 0, 1] * Multiplicative.toAdd Y *
          (1 : Matrix (Fin 2) (Fin 2) K)ᵀ = Multiplicative.toAdd Y := by
        have := congrArg Multiplicative.toAdd (hY (u1 K, 1) ⟨u1_mem, (uni K).one_mem⟩)
        rw [toAdd_rho] at this
        exact this
      have h11 := congrFun (congrFun h1 0) 1
      rw [mul_mul_transpose_apply] at h11
      simp at h11
      rw [h11, map_zero]
  · obtain ⟨γ, μ, hμ, hγ⟩ := exists_rho_eq_smul_J hdet
    have hmem := mem_map_rho_iff hw γ
    simp only [hγ, detPolar_smul_J] at hmem
    refine ⟨γ, (uni K).map ((MonoidHom.id _).prod (MonoidHom.id _)), ?_, fun c => ?_,
      fun p hp Y hY => ?_, fun Y hY => ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨hu, hu⟩
    · rw [hmem]
      simp
    · rw [hmem] at hY ⊢
      obtain ⟨u, hu, rfl⟩ := hp
      obtain ⟨c, hc⟩ := mem_uni_iff.mp hu
      rw [toAdd_rho]
      simp only [MonoidHom.prod_apply, MonoidHom.id_apply, hc]
      rw [mul_mul_transpose_apply, mul_mul_transpose_apply]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, mul_zero, zero_mul, one_mul,
        zero_add]
      convert hY using 3
      linear_combination c * Multiplicative.toAdd Y 1 1 * h2
    · rw [hmem]
      have h1 : !![(1 : K), 1; 0, 1] * Multiplicative.toAdd Y * !![(1 : K), 1; 0, 1]ᵀ =
          Multiplicative.toAdd Y := by
        have := congrArg Multiplicative.toAdd (hY (u1 K, u1 K) ⟨u1 K, u1_mem, rfl⟩)
        rw [toAdd_rho] at this
        exact this
      have e01 := congrFun (congrFun h1 0) 1
      have e00 := congrFun (congrFun h1 0) 0
      rw [mul_mul_transpose_apply] at e01 e00
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, mul_zero, one_mul,
        zero_add] at e01 e00
      have h11 : Multiplicative.toAdd Y 1 1 = 0 := by linear_combination e01
      have hs : Multiplicative.toAdd Y 1 0 + Multiplicative.toAdd Y 0 1 = 0 := by
        linear_combination e00 - h11
      rw [hs, mul_zero, map_zero]

end CFSG.Quasithin.H13.Ch9
