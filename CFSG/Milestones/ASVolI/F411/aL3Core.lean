module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

section L3Sylow

variable {K : Type} [Field K]

@[expose] def burnsideF411a_x01 (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def burnsideF411a_x12 (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, t; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem burnsideF411a_coe_x01 (t : K) :
    (burnsideF411a_x01 t : Matrix (Fin 3) (Fin 3) K) = !![1, t, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem burnsideF411a_coe_x12 (t : K) :
    (burnsideF411a_x12 t : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, t; 0, 0, 1] :=
  rfl

theorem burnsideF411a_x01_mem (t : K) : burnsideF411a_x01 t ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [burnsideF411a_coe_x01]
  · fin_cases i <;> simp [burnsideF411a_coe_x01]

theorem burnsideF411a_x12_mem (t : K) : burnsideF411a_x12 t ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [burnsideF411a_coe_x12]
  · fin_cases i <;> simp [burnsideF411a_coe_x12]

theorem burnsideF411a_x01_inv (t : K) : (burnsideF411a_x01 t)⁻¹ = burnsideF411a_x01 (-t) := by
  refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, burnsideF411a_coe_x01, burnsideF411a_coe_x01,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem burnsideF411a_x12_inv (t : K) : (burnsideF411a_x12 t)⁻¹ = burnsideF411a_x12 (-t) := by
  refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, burnsideF411a_coe_x12, burnsideF411a_coe_x12,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem burnsideF411a_eq_of_proj_eq (p : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ} (hn : 1 ≤ n)
    {g u : SpecialLinearGroup (Fin n) K} (m : ℕ) (hg : g ^ p ^ m = 1) (hu : u ^ p ^ m = 1)
    (h : proj n K g = proj n K u) : g = u := by
  have hz : g⁻¹ * u ∈ scalars n K := proj_eq_proj_iff.mp h
  have hcen := scalars_le_center n K hz
  obtain ⟨c, -, hc⟩ := hz
  have hu' : u = g * (g⁻¹ * u) := by rw [mul_inv_cancel_left]
  have hzN : (g⁻¹ * u) ^ p ^ m = 1 := by
    have hcomm : Commute g (g⁻¹ * u) := Subgroup.mem_center_iff.mp hcen g
    have h2 := hcomm.mul_pow (p ^ m)
    rw [← hu', hu, hg, one_mul] at h2
    exact h2.symm
  have hmat : (((g⁻¹ * u) ^ p ^ m : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) ((c : K) ^ p ^ m) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow]
  rw [hzN, Matrix.SpecialLinearGroup.coe_one] at hmat
  have hc1 : (c : K) ^ p ^ m = 1 := by
    have h3 := congrFun (congrFun hmat ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h3.symm
  have hc2 : (c : K) = 1 := by
    have h0 : ((c : K) - 1) ^ p ^ m = 0 := by rw [sub_pow_char_pow, hc1, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h0)
  have hz1 : g⁻¹ * u = 1 := by
    ext i j
    rw [hc, hc2, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [hu', hz1, mul_one]

theorem burnsideF411a_isPGroup_unitriangular [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) : IsPGroup p (unitriangular n K) := by
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hk
  exact IsPGroup.of_card (n := k * (n * (n - 1) / 2)) (by rw [card_unitriangular, hk, pow_mul])

theorem burnsideF411a_fix_of_descend [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (e : MulAut (SpecialLinearGroup (Fin 3) K))
    (he : ∀ x ∈ projUnitriangular 3 K, descendAut 3 K e x = x) :
    ∀ u ∈ unitriangular 3 K, e u = u := by
  intro u hu
  obtain ⟨m, hm⟩ := burnsideF411a_isPGroup_unitriangular (K := K) p 3 ⟨u, hu⟩
  have hum : u ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  refine burnsideF411a_eq_of_proj_eq p (by norm_num) m ?_ hum ?_
  · rw [← map_pow, hum, map_one]
  · rw [← descendAut_proj, he _ (Subgroup.mem_map_of_mem _ hu)]

@[expose] noncomputable def burnsideF411a_slAut (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ) :
    MulAut (SpecialLinearGroup (Fin 3) K) :=
  CatalogueBHigherLinearAction.slConjugation 3 K A *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ * CatalogueBGraphForm.slGraphAut 3 K ^ ε

theorem burnsideF411a_descend_slAut (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ) :
    conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε =
      descendAut 3 K (burnsideF411a_slAut A σ ε) := by
  rw [burnsideF411a_slAut, map_mul, map_mul, map_pow]
  rfl

theorem burnsideF411a_coe_slAut (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ)
    (u : SpecialLinearGroup (Fin 3) K) :
    ((burnsideF411a_slAut A σ ε u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) *
        ((((CatalogueBGraphForm.slGraphAut 3 K ^ ε) u : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).map σ) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [burnsideF411a_slAut, MulAut.mul_apply, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  rfl

theorem burnsideF411a_intertwine {A : GL (Fin 3) K} {X Y : Matrix (Fin 3) (Fin 3) K}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * X * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Y) :
    (A : Matrix (Fin 3) (Fin 3) K) * X = Y * (A : Matrix (Fin 3) (Fin 3) K) := by
  rw [← h, Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), Units.inv_mul,
    Matrix.mul_one]

theorem burnsideF411a_map_x01 (σ : K ≃+* K) (t : K) :
    (burnsideF411a_x01 t : Matrix (Fin 3) (Fin 3) K).map σ = burnsideF411a_x01 (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF411a_coe_x01]

theorem burnsideF411a_map_x12 (σ : K ≃+* K) (t : K) :
    (burnsideF411a_x12 t : Matrix (Fin 3) (Fin 3) K).map σ = burnsideF411a_x12 (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF411a_coe_x12]

theorem burnsideF411a_coe_slGraphAut (u : SpecialLinearGroup (Fin 3) K) :
    ((CatalogueBGraphForm.slGraphAut 3 K u : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      ((u⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ :=
  rfl

theorem burnsideF411a_graph_x01 (σ : K ≃+* K) (t : K) :
    ((CatalogueBGraphForm.slGraphAut 3 K (burnsideF411a_x01 t) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).map σ =
      ((burnsideF411a_x01 (-σ t) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by
  rw [burnsideF411a_coe_slGraphAut, burnsideF411a_x01_inv, Matrix.transpose_map,
    burnsideF411a_map_x01, map_neg]

theorem burnsideF411a_graph_x12 (σ : K ≃+* K) (t : K) :
    ((CatalogueBGraphForm.slGraphAut 3 K (burnsideF411a_x12 t) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).map σ =
      ((burnsideF411a_x12 (-σ t) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by
  rw [burnsideF411a_coe_slGraphAut, burnsideF411a_x12_inv, Matrix.transpose_map,
    burnsideF411a_map_x12, map_neg]

theorem burnsideF411a_inner_of_fix_projUnitriangular [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (β : MulAut (projectiveSL 3 K)) (hβ : ∀ x ∈ projUnitriangular 3 K, β x = x) :
    ∃ g, β = MulAut.conj g := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  rw [burnsideF411a_descend_slAut] at hβ
  have hfix := burnsideF411a_fix_of_descend p _ hβ
  have hint : ∀ u ∈ unitriangular 3 K, (A : Matrix (Fin 3) (Fin 3) K) *
      ((((CatalogueBGraphForm.slGraphAut 3 K ^ ε) u : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).map σ) =
        (u : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
    intro u hu
    apply burnsideF411a_intertwine
    rw [← burnsideF411a_coe_slAut, hfix u hu]
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    simp only [pow_zero, MulAut.one_apply] at hint
    have h1 := hint _ (burnsideF411a_x01_mem 1)
    have h2 := hint _ (burnsideF411a_x12_mem 1)
    have h3 : ∀ t : K, (A : Matrix (Fin 3) (Fin 3) K) * burnsideF411a_x01 (σ t) =
        burnsideF411a_x01 t * (A : Matrix (Fin 3) (Fin 3) K) := fun t => by
      rw [← burnsideF411a_map_x01]
      exact hint _ (burnsideF411a_x01_mem t)
    rw [burnsideF411a_map_x01, map_one] at h1
    rw [burnsideF411a_map_x12, map_one] at h2
    generalize hM : (A : Matrix (Fin 3) (Fin 3) K) = M at hdet h1 h2 h3
    have m10 : M 1 0 = 0 := by
      have e : M 1 0 * 1 + M 1 1 * 1 + M 1 2 * 0 = 0 * M 0 1 + 1 * M 1 1 + 0 * M 2 1 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x01] using
          congrFun (congrFun h1 1) 1
      linear_combination e
    have m20 : M 2 0 = 0 := by
      have e : M 2 0 * 1 + M 2 1 * 1 + M 2 2 * 0 = 0 * M 0 1 + 0 * M 1 1 + 1 * M 2 1 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x01] using
          congrFun (congrFun h1 2) 1
      linear_combination e
    have m00 : M 0 0 = M 1 1 := by
      have e : M 0 0 * 1 + M 0 1 * 1 + M 0 2 * 0 = 1 * M 0 1 + 1 * M 1 1 + 0 * M 2 1 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x01] using
          congrFun (congrFun h1 0) 1
      linear_combination e
    have m12 : M 1 2 = 0 := by
      have e : M 0 0 * 0 + M 0 1 * 0 + M 0 2 * 1 = 1 * M 0 2 + 1 * M 1 2 + 0 * M 2 2 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x01] using
          congrFun (congrFun h1 0) 2
      linear_combination -e
    have m01 : M 0 1 = 0 := by
      have e : M 0 0 * 0 + M 0 1 * 1 + M 0 2 * 1 = 1 * M 0 2 + 0 * M 1 2 + 0 * M 2 2 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x12] using
          congrFun (congrFun h2 0) 2
      linear_combination e
    have m21 : M 2 1 = 0 := by
      have e : M 2 0 * 0 + M 2 1 * 1 + M 2 2 * 1 = 0 * M 0 2 + 0 * M 1 2 + 1 * M 2 2 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x12] using
          congrFun (congrFun h2 2) 2
      linear_combination e
    have m22 : M 2 2 = M 1 1 := by
      have e : M 1 0 * 0 + M 1 1 * 1 + M 1 2 * 1 = 0 * M 0 2 + 1 * M 1 2 + 1 * M 2 2 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x12] using
          congrFun (congrFun h2 1) 2
      linear_combination -e
    have hdetM : M.det = M 1 1 ^ 3 := by
      rw [Matrix.det_fin_three, m00, m22, m10, m20, m01, m12, m21]
      ring
    have ha : M 1 1 ≠ 0 := by
      intro h0
      apply hdet
      rw [hdetM, h0]
      ring
    have hσt : ∀ t : K, σ t = t := by
      intro t
      have e : M 0 0 * σ t + M 0 1 * 1 + M 0 2 * 0 = 1 * M 0 1 + t * M 1 1 + 0 * M 2 1 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x01] using
          congrFun (congrFun (h3 t) 0) 1
      have e2 : M 1 1 * (σ t - t) = 0 := by linear_combination e - σ t * m00
      exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left ha)
    have hσ : σ = 1 := RingEquiv.ext fun t => by rw [hσt t]; rfl
    rw [hσ, map_one, pow_zero, mul_one, mul_one]
    obtain ⟨g, hg⟩ := conjAut_mem_range_conj_of_det_eq_pow (A := A) (μ := Units.mk0 (M 1 1) ha)
      (by
        ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hM,
          hdetM])
    exact ⟨g, hg.symm⟩
  ·
    exfalso
    simp only [pow_one] at hint
    have h1 := hint _ (burnsideF411a_x01_mem 1)
    have h2 := hint _ (burnsideF411a_x12_mem 1)
    rw [burnsideF411a_graph_x01, map_one] at h1
    rw [burnsideF411a_graph_x12, map_one] at h2
    generalize hM : (A : Matrix (Fin 3) (Fin 3) K) = M at hdet h1 h2
    have m21 : M 2 1 = 0 := by
      have e : M 2 0 * 1 + M 2 1 * -1 + M 2 2 * 0 = 0 * M 0 0 + 0 * M 1 0 + 1 * M 2 0 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x01] using
          congrFun (congrFun h1 2) 0
      linear_combination -e
    have m20 : M 2 0 = 0 := by
      have e : M 1 0 * 1 + M 1 1 * 0 + M 1 2 * 0 = 0 * M 0 0 + 1 * M 1 0 + 1 * M 2 0 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x12] using
          congrFun (congrFun h2 1) 0
      linear_combination -e
    have m22 : M 2 2 = 0 := by
      have e : M 1 0 * 0 + M 1 1 * 0 + M 1 2 * 1 = 0 * M 0 2 + 1 * M 1 2 + 1 * M 2 2 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_three, burnsideF411a_coe_x12] using
          congrFun (congrFun h2 1) 2
      linear_combination -e
    exact hdet (by rw [Matrix.det_fin_three, m20, m21, m22]; ring)

theorem burnsideF411a_finite_projSL [Finite K] (n : ℕ) : Finite (projectiveSL n K) := by
  infer_instance

theorem burnsideF411a_projSL3_inner_of_fix_sylow [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (α : MulAut (projectiveSL 3 K)) (S : Sylow p (projectiveSL 3 K))
    (hα : ∀ s ∈ (S : Subgroup (projectiveSL 3 K)), α s = s) : ∃ g, α = MulAut.conj g := by
  haveI := burnsideF411a_finite_projSL (K := K) 3
  obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) P₀ S
  have hβ : ∀ u ∈ projUnitriangular 3 K, ((MulAut.conj x)⁻¹ * α * MulAut.conj x) u = u := by
    intro u hu
    have hxu : x * u * x⁻¹ ∈ (S : Subgroup (projectiveSL 3 K)) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      have h1 := Subgroup.smul_mem_pointwise_smul u (MulAut.conj x) (P₀ : Subgroup _)
        (by rw [hP₀]; exact hu)
      rwa [MulAut.smul_def, MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ hxu, MulAut.conj_inv_apply]
    group
  obtain ⟨g, hg⟩ := burnsideF411a_inner_of_fix_projUnitriangular p _ hβ
  refine ⟨x * g * x⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg]
  group

end L3Sylow

end CFSG.ASVolI
