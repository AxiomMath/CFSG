module

public import CFSG.GH74.GLS.C3.Layer2.InvolutionExt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

theorem s16c11_case5_rhoU_injective [CharP K 2] {a b a' b' : K}
    (h : s16c11_case5_rhoU a b = s16c11_case5_rhoU a' b') : a = a' ∧ b = b' := by
  have h' : (s16c11_case5_u a, s16c11_case5_u b) =
      (s16c11_case5_u a', s16c11_case5_u b') :=
    rho_injective (by simpa only [s16c11_case5_rhoU] using h)
  rw [Prod.mk.injEq] at h'
  exact ⟨s16c11_case5_u_injective h'.1, s16c11_case5_u_injective h'.2⟩

theorem s16c11_case5_sigma_conj_rhoU (a b : K) :
    s16c11_case5_sigma * s16c11_case5_rhoU a b * s16c11_case5_sigma =
      s16c11_case5_rhoU b a := by
  change (trM : MulAut (VM K)) * s16c11_case5_rhoU (K := K) a b * trM =
    s16c11_case5_rhoU (K := K) b a
  rw [s16c11_case5_rhoU, s16c11_case5_rhoU, rho_apply, rho_apply, trM_lr, mul_assoc,
    trM_mul_self, mul_one]

private theorem s16c11_case5_sa_eq [CharP K 2] (a : K) :
    s16c11_case5_sa a = s16c11_case5_rhoU a a * s16c11_case5_sigma := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  show Multiplicative.toAdd (s16c11_case5_sa a
      (Multiplicative.ofAdd (Multiplicative.toAdd X))) =
    Multiplicative.toAdd ((s16c11_case5_rhoU a a * s16c11_case5_sigma (K := K))
      (Multiplicative.ofAdd (Multiplicative.toAdd X)))
  rw [MulAut.mul_apply, s16c11_case5_sigma_ofAdd, s16c11_case5_rhoU_toAdd,
    s16c11_case5_sa_toAdd]

theorem s16c11_case5_sa_sq [CharP K 2] (a : K) :
    s16c11_case5_sa a * s16c11_case5_sa a = 1 := by
  rw [s16c11_case5_sa_eq]
  calc (s16c11_case5_rhoU a a * s16c11_case5_sigma) *
        (s16c11_case5_rhoU a a * s16c11_case5_sigma)
      = s16c11_case5_rhoU a a *
          (s16c11_case5_sigma * s16c11_case5_rhoU a a * s16c11_case5_sigma) := by group
    _ = s16c11_case5_rhoU a a * s16c11_case5_rhoU a a := by
        rw [s16c11_case5_sigma_conj_rhoU]
    _ = s16c11_case5_rhoU (a + a) (a + a) := s16c11_case5_rhoU_mul a a a a
    _ = s16c11_case5_rhoU 0 0 := by rw [CharTwo.add_self_eq_zero]
    _ = 1 := s16c11_case5_rhoU_one

theorem s16c11_case5_card_V (hK : Nat.card K = 4) :
    Nat.card ↥(s16c11_case5_V (K := K)) = 16 := by
  haveI := s16c11_case5_charP hK
  have hinj : Function.Injective (fun p : K × K => s16c11_case5_rhoU p.1 p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := s16c11_case5_rhoU_injective h
    exact Prod.ext h1 h2
  change Nat.card (Set.range (fun p : K × K => s16c11_case5_rhoU p.1 p.2)) = 16
  rw [Nat.card_range_of_injective hinj, Nat.card_prod, hK]

theorem s16c11_case5_mem_S0 {x : MulAut (VM K)} :
    x ∈ s16c11_case5_S0 (K := K) ↔
      ∃ a b : K, x = s16c11_case5_rhoU a b ∨
        x = s16c11_case5_rhoU a b * s16c11_case5_sigma := by
  have haN : ∀ t ∈ s16c11_case5_V (K := K),
      s16c11_case5_sigma * t * s16c11_case5_sigma⁻¹ ∈ s16c11_case5_V := by
    intro t ht
    rw [s16c11_case5_mem_V] at ht ⊢
    obtain ⟨⟨a, b⟩, rfl⟩ := ht
    refine ⟨(b, a), ?_⟩
    rw [inv_eq_of_mul_eq_one_right (trM_mul_self (K := K)), s16c11_case5_sigma_conj_rhoU]
  have ha2 : s16c11_case5_sigma (K := K) ^ 2 = 1 := by
    rw [pow_two, trM_mul_self]
  rw [s16c11_case5_S0, CFSG.GH74.GLS.C3.Layer2.mem_sup_zpowers_iff haN ha2]
  constructor
  · rintro (h | h)
    · rw [s16c11_case5_mem_V] at h
      obtain ⟨⟨a, b⟩, rfl⟩ := h
      exact ⟨a, b, Or.inl rfl⟩
    · rw [s16c11_case5_mem_V] at h
      obtain ⟨⟨a, b⟩, hab⟩ := h
      refine ⟨a, b, Or.inr ?_⟩
      rw [← hab, mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨a, b, h | h⟩
    · left
      rw [s16c11_case5_mem_V]
      exact ⟨(a, b), h⟩
    · right
      rw [s16c11_case5_mem_V]
      refine ⟨(a, b), ?_⟩
      rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem s16c11_case5_mem_fixV_rhoU_iff' (a b : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.ofAdd X ∈ fixV (Subgroup.zpowers (s16c11_case5_rhoU a b)) ↔
      a * X 1 1 = 0 ∧ b * X 1 1 = 0 ∧ a * X 1 0 + b * X 0 1 = 0 := by
  rw [s16c11_case5_mem_fixV_rhoU_iff, s16c11_case5_fix_conds]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have hzero : a * b * X 1 1 = 0 := by rw [mul_assoc, h2, mul_zero]
    rwa [hzero, add_zero] at h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have hzero : a * b * X 1 1 = 0 := by rw [mul_assoc, h2, mul_zero]
    rw [hzero, add_zero]
    exact h3

theorem s16c11_case5_mem_fixV_iff_of_le_V {A : Subgroup (MulAut (VM K))}
    (hAV : A ≤ s16c11_case5_V) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.ofAdd X ∈ fixV A ↔
      ∀ a b : K, s16c11_case5_rhoU a b ∈ A →
        a * X 1 1 = 0 ∧ b * X 1 1 = 0 ∧ a * X 1 0 + b * X 0 1 = 0 := by
  constructor
  · intro hX a b hab
    rw [← s16c11_case5_mem_fixV_rhoU_iff']
    exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr
      (CFSG.Quasithin.mem_fixV.mp hX (s16c11_case5_rhoU a b) hab)
  · intro hX
    rw [CFSG.Quasithin.mem_fixV]
    intro x hx
    obtain ⟨⟨a, b⟩, rfl⟩ := s16c11_case5_mem_V.mp (hAV hx)
    rw [← CFSG.Quasithin.mem_fixV_zpowers_iff_apply,
      s16c11_case5_mem_fixV_rhoU_iff']
    exact hX a b hx

private theorem s16c11_case5_D0Hom_toAdd (μ : Kˣ) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.toAdd (s16c11_case5_D0Hom μ (Multiplicative.ofAdd X)) =
      (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) * X *
        (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have hD : s16c11_case5_D0Hom μ = rho (s16c11_case5_t μ, s16c11_case5_t μ) := rfl
  rw [hD, rho_apply, toAdd_lr]
  rfl

private theorem s16c11_case5_t_apply_00 (μ : Kˣ) :
    (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) 0 0 = (μ : K) := by
  rw [s16c11_case5_t, SpecialLinearGroup.diag2_coe']
  simp

private theorem s16c11_case5_t_apply_01 (μ : Kˣ) :
    (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
  rw [s16c11_case5_t, SpecialLinearGroup.diag2_coe']
  simp

private theorem s16c11_case5_t_apply_10 (μ : Kˣ) :
    (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [s16c11_case5_t, SpecialLinearGroup.diag2_coe']
  simp

private theorem s16c11_case5_t_apply_11 (μ : Kˣ) :
    (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) 1 1 = (μ : K)⁻¹ := by
  rw [s16c11_case5_t, SpecialLinearGroup.diag2_coe']
  simp

private theorem s16c11_case5_t_mul_transpose_00 (μ : Kˣ) :
    ((s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) *
      (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 =
      (μ : K) * (μ : K) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    s16c11_case5_t_apply_00, s16c11_case5_t_apply_01, mul_zero, zero_mul, add_zero, zero_add]

private theorem s16c11_case5_t_mul_transpose_11 (μ : Kˣ) :
    ((s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K) *
      (s16c11_case5_t μ : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 1 =
      (μ : K)⁻¹ * (μ : K)⁻¹ := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    s16c11_case5_t_apply_10, s16c11_case5_t_apply_11, mul_zero, zero_mul, add_zero, zero_add]

private theorem s16c11_case5_scalar_apply_00 (c : Kˣ) :
    ((Matrix.scalar (Fin 2) (α := K)).toMonoidHom (c : K)) 0 0 = (c : K) := by
  change (Matrix.scalar (Fin 2) (c : K)) 0 0 = (c : K)
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]

private theorem s16c11_case5_scalar_apply_11 (c : Kˣ) :
    ((Matrix.scalar (Fin 2) (α := K)).toMonoidHom (c : K)) 1 1 = (c : K) := by
  change (Matrix.scalar (Fin 2) (c : K)) 1 1 = (c : K)
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem s16c11_case5_D0Hom_injective (hK : Nat.card K = 4) :
    Function.Injective (s16c11_case5_D0Hom (K := K)) := by
  haveI := s16c11_case5_charP hK
  intro μ ν h
  have ht : s16c11_case5_t μ = s16c11_case5_t ν := by
    have hp : (s16c11_case5_t μ, s16c11_case5_t μ) =
        (s16c11_case5_t ν, s16c11_case5_t ν) :=
      rho_injective (show rho (s16c11_case5_t μ, s16c11_case5_t μ) =
        rho (s16c11_case5_t ν, s16c11_case5_t ν) from h)
    exact (Prod.ext_iff.mp hp).1
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) ht
  simp only [s16c11_case5_t_apply_00] at h2
  exact Units.ext h2

theorem s16c11_case5_card_D0 (hK : Nat.card K = 4) :
    Nat.card ↥(s16c11_case5_D0 (K := K)) = 3 := by
  rw [s16c11_case5_D0, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    (s16c11_case5_D0Hom_injective hK), Subgroup.card_top, Nat.card_units, hK]

private noncomputable def s16c11_case5_scalMulCoord (K : Type) [Field K] :
    Kˣ →* MulAut (VM K) where
  toFun c := lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
  map_one' := by rw [map_one, lr_one]
  map_mul' c d := by rw [map_mul, lr_mul, mul_one]

private theorem s16c11_case5_scalMul_eq_range_coord (K : Type) [Field K] :
    s16c11C5Scal K = (s16c11_case5_scalMulCoord K).range := by
  rw [s16c11C5Scal]
  have h : {x : MulAut (VM K) | ∃ c : Kˣ,
      x = lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1} =
      Set.range (s16c11_case5_scalMulCoord K) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range, s16c11_case5_scalMulCoord]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [h, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem s16c11_case5_D0_inf_Scal (hK : Nat.card K = 4) :
    s16c11_case5_D0 (K := K) ⊓ s16c11C5Scal K = ⊥ := by
  haveI := s16c11_case5_charP hK
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxD, hxZ⟩ := hx
  rw [s16c11_case5_D0, MonoidHom.mem_range] at hxD
  obtain ⟨μ, hμ⟩ := hxD
  subst hμ
  rw [s16c11_case5_scalMul_eq_range_coord, MonoidHom.mem_range] at hxZ
  obtain ⟨c, hc⟩ := hxZ
  have hc' : s16c11_case5_D0Hom μ =
      lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1 := by
    rw [← hc]
    rfl
  have h1 := congrArg (fun f : MulAut (VM K) =>
    Multiplicative.toAdd (f (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K)))) hc'
  simp only [s16c11_case5_D0Hom_toAdd, toAdd_lr, toAdd_ofAdd, Units.val_one, Matrix.mul_one,
    Matrix.transpose_one, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.coe_map] at h1
  have h00 : (μ : K) * (μ : K) = (c : K) := by
    have h := congrFun (congrFun h1 0) 0
    rw [s16c11_case5_t_mul_transpose_00, s16c11_case5_scalar_apply_00] at h
    exact h
  have h11 : (μ : K)⁻¹ * (μ : K)⁻¹ = (c : K) := by
    have h := congrFun (congrFun h1 1) 1
    rw [s16c11_case5_t_mul_transpose_11, s16c11_case5_scalar_apply_11] at h
    exact h
  have h4 : (μ : K) ^ 4 = 1 := by
    have hc : (μ : K) * (μ : K) = ((μ : K) * (μ : K))⁻¹ := by
      calc (μ : K) * (μ : K) = (c : K) := h00
        _ = (μ : K)⁻¹ * (μ : K)⁻¹ := h11.symm
        _ = ((μ : K) * (μ : K))⁻¹ := (_root_.mul_inv_rev (μ : K) (μ : K)).symm
    have hmm : ((μ : K) * (μ : K)) * ((μ : K) * (μ : K)) = 1 := by
      nth_rewrite 1 [hc]
      exact inv_mul_cancel₀ (mul_ne_zero μ.ne_zero μ.ne_zero)
    calc (μ : K) ^ 4 = ((μ : K) * (μ : K)) * ((μ : K) * (μ : K)) := by ring
      _ = 1 := hmm
  have h3 : (μ : K) ^ 3 = 1 := by
    have h3u : μ ^ 3 = 1 := by
      have := pow_card_eq_one' (x := μ)
      rw [Nat.card_units, hK] at this
      simpa using this
    have := congrArg (fun u : Kˣ => (u : K)) h3u
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    exact this
  have hmu : (μ : K) = 1 := by
    have h43 : (μ : K) ^ 4 = (μ : K) ^ 3 * (μ : K) := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
    rw [h4, h3, one_mul] at h43
    exact h43.symm
  have hμ1 : μ = 1 := Units.ext hmu
  rw [hμ1]
  exact map_one _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
