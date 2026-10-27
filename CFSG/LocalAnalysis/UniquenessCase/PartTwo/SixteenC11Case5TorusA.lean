module

public import CFSG.Quasithin.Background.HOm4Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

theorem s16c11_case5_charP (hK : Nat.card K = 4) : CharP K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)

@[expose] def s16c11_case5_u (a : K) : SpecialLinearGroup (Fin 2) K := tv 0 1 (by decide) a

theorem s16c11_case5_u_zero : s16c11_case5_u (K := K) 0 = 1 := by
  ext
  simp [s16c11_case5_u, tv, Matrix.transvection]

theorem s16c11_case5_u_mul (a b : K) :
    s16c11_case5_u a * s16c11_case5_u b = s16c11_case5_u (a + b) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, s16c11_case5_u, tv]
  exact Matrix.transvection_mul_transvection_same 0 1 (by decide) a b

theorem s16c11_case5_u_injective : Function.Injective (s16c11_case5_u (K := K)) := by
  intro a b h
  have h2 : Matrix.transvection (0 : Fin 2) 1 a = Matrix.transvection 0 1 b := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
    simpa [s16c11_case5_u, tv] using this
  have := congrFun (congrFun h2 0) 1
  simpa [Matrix.transvection] using this

@[expose] noncomputable def s16c11_case5_rhoU (a b : K) : MulAut (VM K) :=
  rho (s16c11_case5_u a, s16c11_case5_u b)

theorem s16c11_case5_rhoU_mul (a b a' b' : K) :
    s16c11_case5_rhoU a b * s16c11_case5_rhoU a' b' =
      s16c11_case5_rhoU (a + a') (b + b') := by
  rw [s16c11_case5_rhoU, s16c11_case5_rhoU, s16c11_case5_rhoU, ← map_mul,
    Prod.mk_mul_mk, s16c11_case5_u_mul, s16c11_case5_u_mul]

theorem s16c11_case5_rhoU_one : s16c11_case5_rhoU (K := K) 0 0 = 1 := by
  rw [s16c11_case5_rhoU, s16c11_case5_u_zero, Prod.mk_one_one, map_one]

theorem s16c11_case5_rhoU_inv (a b : K) :
    (s16c11_case5_rhoU a b)⁻¹ = s16c11_case5_rhoU (-a) (-b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [s16c11_case5_rhoU_mul a b (-a) (-b), add_neg_cancel, add_neg_cancel,
    s16c11_case5_rhoU_one]

@[expose] noncomputable def s16c11_case5_V : Subgroup (MulAut (VM K)) :=
  { carrier := Set.range (fun p : K × K => s16c11_case5_rhoU p.1 p.2)
    one_mem' := ⟨(0, 0), s16c11_case5_rhoU_one⟩
    mul_mem' := by
      rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨(p.1 + q.1, p.2 + q.2), by rw [s16c11_case5_rhoU_mul]⟩
    inv_mem' := by
      rintro _ ⟨p, rfl⟩
      exact ⟨(-p.1, -p.2), (s16c11_case5_rhoU_inv p.1 p.2).symm⟩ }

theorem s16c11_case5_mem_V {x : MulAut (VM K)} :
    x ∈ s16c11_case5_V ↔ ∃ p : K × K, x = s16c11_case5_rhoU p.1 p.2 := by
  constructor
  · intro hx
    change x ∈ Set.range (fun p : K × K => s16c11_case5_rhoU p.1 p.2) at hx
    rw [Set.mem_range] at hx
    exact hx.imp fun p => Eq.symm
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩

theorem s16c11_case5_rhoU_mem_V (a b : K) :
    s16c11_case5_rhoU a b ∈ s16c11_case5_V := ⟨(a, b), rfl⟩

theorem s16c11_case5_V_le_range : s16c11_case5_V ≤ (rho (K := K)).range := by
  rintro x ⟨⟨a, b⟩, rfl⟩
  exact ⟨(s16c11_case5_u a, s16c11_case5_u b), rfl⟩

@[expose] noncomputable def s16c11_case5_t (μ : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.diag2 (μ : K) μ.ne_zero

theorem s16c11_case5_t_mul (μ ν : Kˣ) :
    s16c11_case5_t μ * s16c11_case5_t ν = s16c11_case5_t (μ * ν) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, s16c11_case5_t,
    SpecialLinearGroup.diag2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem s16c11_case5_t_one : s16c11_case5_t (K := K) 1 = 1 := by
  apply Subtype.ext
  simp only [s16c11_case5_t]
  rw [SpecialLinearGroup.diag2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] noncomputable def s16c11_case5_D0Hom : Kˣ →* MulAut (VM K) where
  toFun μ := rho (s16c11_case5_t μ, s16c11_case5_t μ)
  map_one' := by rw [s16c11_case5_t_one, Prod.mk_one_one, map_one]
  map_mul' μ ν := by rw [← s16c11_case5_t_mul, ← map_mul, Prod.mk_mul_mk]

@[expose] noncomputable def s16c11_case5_D0 : Subgroup (MulAut (VM K)) :=
  s16c11_case5_D0Hom.range

theorem s16c11_case5_D0_le_range : s16c11_case5_D0 ≤ (rho (K := K)).range := by
  rintro x hx
  rw [s16c11_case5_D0, MonoidHom.mem_range] at hx
  obtain ⟨μ, rfl⟩ := hx
  exact ⟨(s16c11_case5_t μ, s16c11_case5_t μ), rfl⟩

section Fixed

theorem s16c11_case5_rhoU_toAdd (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.toAdd (s16c11_case5_rhoU a b (Multiplicative.ofAdd X)) =
      (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [s16c11_case5_rhoU, rho_apply, toAdd_lr]
  rfl

theorem s16c11_case5_mem_fixV_rhoU_iff (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.ofAdd X ∈ fixV (Subgroup.zpowers (s16c11_case5_rhoU a b)) ↔
      (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
  rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
  constructor
  · intro h
    have h2 := congrArg Multiplicative.toAdd h
    rwa [s16c11_case5_rhoU_toAdd] at h2
  · intro h
    apply Multiplicative.toAdd.injective
    rw [s16c11_case5_rhoU_toAdd, h]
    rfl

theorem s16c11_case5_act_entry_00 (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 =
      X 0 0 + a * X 1 0 + b * X 0 1 + a * b * X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]
  ring

theorem s16c11_case5_act_entry_01 (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 =
      X 0 1 + a * X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]

theorem s16c11_case5_act_entry_10 (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 0 =
      X 1 0 + b * X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]

theorem s16c11_case5_act_entry_11 (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 1 =
      X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]

theorem s16c11_case5_fix_conds (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ = X ↔
      a * X 1 1 = 0 ∧ b * X 1 1 = 0 ∧
        a * X 1 0 + b * X 0 1 + a * b * X 1 1 = 0 := by
  constructor
  · intro h
    have h00 : ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 = X 0 0 := by rw [h]
    have h01 : ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 = X 0 1 := by rw [h]
    have h10 : ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 0 = X 1 0 := by rw [h]
    rw [s16c11_case5_act_entry_00] at h00
    rw [s16c11_case5_act_entry_01] at h01
    rw [s16c11_case5_act_entry_10] at h10
    exact ⟨by linear_combination h01, by linear_combination h10,
      by linear_combination h00⟩
  · rintro ⟨h1, h2, h3⟩
    ext i j
    fin_cases i <;> fin_cases j
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 = X 0 0
      rw [s16c11_case5_act_entry_00]
      linear_combination h3
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 = X 0 1
      rw [s16c11_case5_act_entry_01]
      linear_combination h1
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 0 = X 1 0
      rw [s16c11_case5_act_entry_10]
      linear_combination h2
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_u b : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 1 = X 1 1
      rw [s16c11_case5_act_entry_11]

end Fixed

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
