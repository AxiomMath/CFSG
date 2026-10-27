module

public import CFSG.Quasithin.Vol2.KGNatSL3Lev

public section

namespace CFSG.Quasithin.H13.Ch4.SL3Pt

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.LieType.SteinbergBR.BlockPar

variable {F : Type} [Field F]

theorem map_parJR_eq_stabE0 :
    (parJR F (Fin 1) (Fin 2)).map (reindexSL F h12).toMonoidHom = stabE0 F := by
  ext B
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact (mem_parJR12_iff M).mp hM
  · intro hB
    refine ⟨(reindexSL F h12).symm B, (mem_parJR12_iff _).mpr ?_, ?_⟩
    · rw [MulEquiv.apply_symm_apply]
      exact hB
    · exact MulEquiv.apply_symm_apply _ B

theorem stabE0_perfect [Finite F]
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤) :
    ⁅stabE0 F, stabE0 F⁆ = stabE0 F := by
  have hperf : ⁅parJR F (Fin 1) (Fin 2), parJR F (Fin 1) (Fin 2)⁆ = parJR F (Fin 1) (Fin 2) := by
    rw [← perfectCore_parQ12 hSL]
    exact perfectCore_perfect _
  rw [← map_parJR_eq_stabE0, ← Subgroup.map_commutator, hperf]

@[expose] def torMat (μ : Fˣ) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal ![((μ⁻¹ : Fˣ) : F) ^ 2, (μ : F), (μ : F)]

theorem det_torMat (μ : Fˣ) : (torMat μ).det = 1 := by
  rw [torMat, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h : ((μ⁻¹ : Fˣ) : F) * (μ : F) = 1 := by simp
  calc ((μ⁻¹ : Fˣ) : F) ^ 2 * (μ : F) * (μ : F)
      = (((μ⁻¹ : Fˣ) : F) * (μ : F)) * (((μ⁻¹ : Fˣ) : F) * (μ : F)) := by ring
    _ = 1 := by rw [h, one_mul]

@[expose] noncomputable def tor : Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun μ := ⟨torMat μ, det_torMat μ⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torMat]
  map_mul' μ ν := by
    apply Subtype.ext
    change torMat (μ * ν) = torMat μ * torMat ν
    rw [torMat, torMat, torMat, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_pow, mul_comm]

theorem coe_tor (μ : Fˣ) : ((tor μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    torMat μ :=
  rfl

theorem tor_mulVec (μ : Fˣ) (v : Fin 3 → F) :
    ((tor μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![((μ⁻¹ : Fˣ) : F) ^ 2 * v 0, (μ : F) * v 1, (μ : F) * v 2] := by
  rw [coe_tor, torMat]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> rfl

theorem tor_injective : Function.Injective (tor : Fˣ →* SpecialLinearGroup (Fin 3) F) := by
  intro μ ν h
  have h1 := congrFun (congrFun (congrArg (fun B : SpecialLinearGroup (Fin 3) F =>
    (B : Matrix (Fin 3) (Fin 3) F)) h) 1) 1
  simp only [coe_tor, torMat, Matrix.diagonal_apply_eq, Matrix.cons_val_one,
    Matrix.cons_val_zero] at h1
  exact Units.ext h1

theorem tor_mulVec_e0 (μ : Fˣ) :
    ((tor μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
      ((μ⁻¹ : Fˣ) : F) ^ 2 • ![1, 0, 0] := by
  rw [tor_mulVec]
  funext i
  fin_cases i <;> simp

theorem tor_mem_normalizer_stabE0 (μ : Fˣ) :
    tor μ ∈ Subgroup.normalizer ((stabE0 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) := by
  have key : ∀ (ν : Fˣ) (B : SpecialLinearGroup (Fin 3) F), B ∈ stabE0 F →
      tor ν * B * (tor ν)⁻¹ ∈ stabE0 F := by
    intro ν B hB
    rw [mem_stabE0, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← map_inv, tor_mulVec_e0,
      Matrix.mulVec_smul, mem_stabE0.mp hB, Matrix.mulVec_smul, tor_mulVec_e0, smul_smul]
    have : ((ν⁻¹⁻¹ : Fˣ) : F) ^ 2 * ((ν⁻¹ : Fˣ) : F) ^ 2 = 1 := by
      rw [← mul_pow]
      simp
    rw [this, one_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro B
  constructor
  · exact key μ B
  · intro h
    have h2 := key μ⁻¹ _ h
    rw [map_inv, inv_inv] at h2
    simpa [mul_assoc] using h2

theorem lev_conj_tor (μ : Fˣ) (B : Matrix (Fin 3) (Fin 3) F) :
    lev (torMat μ * B * (torMat μ⁻¹)) = lev B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lev, torMat, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    rw [mul_comm (μ : F), mul_inv_cancel_right₀ μ.ne_zero]

theorem leviHom_conj_tor (μ : Fˣ) (B : ↥(stabE0 F)) :
    leviHom F ⟨tor μ * (B : SpecialLinearGroup (Fin 3) F) * (tor μ)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (tor_mem_normalizer_stabE0 μ) B).mp B.2⟩ = leviHom F B := by
  apply Subtype.ext
  rw [leviHom_coe, leviHom_coe]
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← map_inv, coe_tor]
  exact lev_conj_tor μ _

theorem eq_zero_of_tor_mulVec {μ : Fˣ} (hμ : μ ^ 2 ≠ 1) {v : Fin 3 → F}
    (hv : ((tor μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    v = 0 := by
  rw [tor_mulVec] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  have hμ1 : (μ : F) ≠ 1 := by
    intro h
    apply hμ
    ext
    simp [h]
  have hμ2 : ((μ⁻¹ : Fˣ) : F) ^ 2 ≠ 1 := by
    intro h
    apply hμ
    have : ((μ ^ 2 : Fˣ) : F) = 1 := by
      have e : ((μ⁻¹ : Fˣ) : F) ^ 2 * ((μ ^ 2 : Fˣ) : F) = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow,
          Units.val_one]
      rw [h, one_mul] at e
      exact e
    exact Units.ext this
  funext i
  fin_cases i
  · have : (((μ⁻¹ : Fˣ) : F) ^ 2 - 1) * v 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ2)
  · have : ((μ : F) - 1) * v 1 = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ1)
  · have : ((μ : F) - 1) * v 2 = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ1)

theorem tor_inv_transpose (μ : Fˣ) :
    ((((tor μ)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).transpose =
      ((tor μ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [← map_inv, coe_tor, torMat, Matrix.diagonal_transpose]

theorem exists_mulVec_e0 {p : Fin 3 → F} (hp : p ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 3) F,
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = p := by
  by_cases h0 : p 0 = 0
  · by_cases h1 : p 1 = 0
    · have h2 : p 2 ≠ 0 := by
        intro h2
        apply hp
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨⟨!![0, 1, 0; 0, 0, (p 2)⁻¹; p 2, 0, 0], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_three]
        simp [h2]
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1]
    · refine ⟨⟨!![0, -(p 1)⁻¹, 0; p 1, 0, 0; p 2, 0, 1], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_three]
        simp [h1]
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0]
  · refine ⟨⟨!![p 0, 0, 0; p 1, (p 0)⁻¹, 0; p 2, 0, 1], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end CFSG.Quasithin.H13.Ch4.SL3Pt
